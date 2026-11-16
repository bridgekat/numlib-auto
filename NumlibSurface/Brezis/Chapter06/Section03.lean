/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Numlib.Analysis.Normed.Lp.Sequence
import Numlib.Analysis.Normed.Operator.Compact.Banach
import NumlibSurface.Brezis.Chapter06.Section01

/-!
# Brezis, Section 6.3: The spectrum of a compact operator

This module formalizes Section 6.3 of [brezis2011functional] for a bounded operator
$T \in \mathcal{L}(E)$ on a real Banach space $E$. The resolvent set is $\rho(T) = \{\lambda \in
\mathbb{R} : T - \lambda I \text{ is bijective from } E \text{ onto } E\}$, the spectrum is
$\sigma(T) = \mathbb{R} \setminus \rho(T)$, and $EV(T)$ is the set of eigenvalues, the $\lambda$
with $N(T - \lambda I) \neq \{0\}$. Always $EV(T) \subseteq \sigma(T)$, and the inclusion can be
strict (Remark 6); $\sigma(T)$ is compact and lies in $[-\|T\|, \|T\|]$ (Proposition 6.7). For a
compact operator $T$ (Theorem 6.8): $0 \in \sigma(T)$ when $\dim E = \infty$, $\sigma(T) \setminus
\{0\} = EV(T) \setminus \{0\}$, and $\sigma(T) \setminus \{0\}$ is either finite or a sequence of
distinct points that converges to $0$. Conversely, every sequence that converges to $0$ is the
nonzero spectrum of a compact operator, a multiplication operator on $\ell^2$ (Remark 7).

Proposition 6.7 is Mathlib's `spectrum.isCompact` and `spectrum.subset_closedBall_norm`. Theorem 6.8
and Lemma 6.2 specialize the backbone module `Numlib.Analysis.Normed.Operator.Compact.Banach`, and
part (b) is Mathlib's Fredholm alternative `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`. The
examples on $\ell^2$ use the backbone module `Numlib.Analysis.Normed.Lp.Sequence`.

## Main definitions

* Section 6.3, definitions of $\rho(T)$, $\sigma(T)$ and $EV(T)$,
  `Brezis.Chapter06.mem_resolventSet_iff_bijective`,
  `Brezis.Chapter06.mem_spectrum_iff_not_bijective` and
  `Brezis.Chapter06.hasEigenvalue_iff_ker_ne_bot`: the definitions of the source agree with
  Mathlib's.
* Remark 6, `Brezis.Chapter06.rightShift`: the right shift $S_r$ on $\ell^2$.
* Remark 7, `Brezis.Chapter06.multiplicationOperator`: the multiplication operator
  $u \mapsto (\alpha_n u_n)_n$ on $\ell^2$.

## Main results

* `Brezis.Chapter06.exists_equiv_of_mem_resolventSet`: if $\lambda \in \rho(T)$, then
  $(T - \lambda I)^{-1}$ is bounded.
* Remark 6, `Brezis.Chapter06.remark_6_6`: $EV(T) \subseteq \sigma(T)$.
* Remark 6, `Brezis.Chapter06.remark_6_6_rightShift`: $0 \in \sigma(S_r)$ but $0 \notin EV(S_r)$.
* Remark 6, `Brezis.Chapter06.remark_6_6_spectrum_eq_empty_of_sq_eq_neg_one`: an operator with
  $T^2 = -I$ has empty spectrum.
* Remark 6, `Brezis.Chapter06.remark_6_6_rotation`: the rotation by $\pi/2$ of $\mathbb{R}^2$ has
  empty spectrum and no eigenvalue.
* Proposition 6.7, `Brezis.Chapter06.proposition_6_7` and `Brezis.Chapter06.proposition_6_7_subset`:
  $\sigma(T)$ is compact and $\sigma(T) \subseteq [-\|T\|, \|T\|]$.
* Theorem 6.8(a), `Brezis.Chapter06.theorem_6_8_a`: if $T$ is compact and $\dim E = \infty$, then
  $0 \in \sigma(T)$.
* Theorem 6.8(b), `Brezis.Chapter06.theorem_6_8_b`: if $T$ is compact, then $\sigma(T) \setminus
  \{0\} = EV(T) \setminus \{0\}$.
* Theorem 6.8(c), `Brezis.Chapter06.theorem_6_8_c`: if $T$ is compact, then
  $\sigma(T) \setminus \{0\}$ is finite or a sequence of distinct points that converges to $0$.
* Lemma 6.2, `Brezis.Chapter06.lemma_6_2`: a convergent sequence of distinct points of
  $\sigma(T) \setminus \{0\}$ has the limit $0$.
* Remark 7, `Brezis.Chapter06.remark_6_7_isCompactOperator` and
  `Brezis.Chapter06.remark_6_7_spectrum`: for $\alpha_n \to 0$ the multiplication operator is
  compact, with $\sigma(T) = \{\alpha_n\} \cup \{0\}$.
* Comments on Chapter 6, item 3, `Brezis.Chapter06.ascent_stabilizes`: for $T$ compact and
  $\lambda \in \sigma(T) \setminus \{0\}$, the kernels $N((T - \lambda I)^k)$ increase strictly up
  to a finite index and are then constant.

## Conventions

* The resolvent set $\rho(T)$ is `resolventSet ℝ T`.
* The spectrum $\sigma(T)$ is `spectrum ℝ T`.
* The condition $\lambda \in EV(T)$ is `Module.End.HasEigenvalue (T : Module.End ℝ E) λ`.
* The space $\ell^2$ is `lp (fun _ : ℕ => ℝ) 2`, with coordinates indexed from $0$; the source
  indexes them from $1$.

## Implementation notes

* Mathlib defines $\lambda \in \rho(T)$ as the invertibility of `algebraMap ℝ _ λ - T` in the
  algebra $\mathcal{L}(E)$. The invertible elements of $\mathcal{L}(E)$ are the bijective operators
  by `ContinuousLinearMap.isUnit_iff_bijective`, which is Corollary 2.7 of the source and needs $E$
  complete.
* The right shift is the backbone's `lp.shiftRightL ℝ`, which Section 11.4 also uses. The
  multiplication operator is the backbone's diagonal operator `lp.diagonalL`.

## Deviations from the source

* **Theorem 6.8(b) and (c)** (generalization). The source assumes $\dim E = \infty$ for all of
  Theorem 6.8. Parts (b) and (c) are stated without this hypothesis. See
  `Brezis.Chapter06.theorem_6_8_b` and `Brezis.Chapter06.theorem_6_8_c`.

## Not formalized

* **Remark 7, the dimension of $N(T)$.** The remark that $N(T)$ may be finite or infinite
  dimensional when $0 \in EV(T)$ is not stated.
-/

open Filter Topology Module.End
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The resolvent set, the spectrum, the eigenvalues -/

/-- **Section 6.3** of [brezis2011functional], definition of the resolvent set. Let $E$ be a Banach
space and $T \in \mathcal{L}(E)$. A real number $\lambda$ is in the resolvent set $\rho(T)$ if
and only if $T - \lambda I$ is bijective from $E$ onto $E$.

Mathlib's `resolventSet ℝ T` is defined by invertibility in $\mathcal{L}(E)$. The equivalence
with bijectivity uses Corollary 2.7 of the source, which needs $E$ complete. -/
theorem mem_resolventSet_iff_bijective [CompleteSpace E] (T : E →L[ℝ] E) (μ : ℝ) :
    μ ∈ resolventSet ℝ T ↔ Function.Bijective (T - μ • (1 : E →L[ℝ] E)) := by
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub, IsUnit.neg_iff,
    ContinuousLinearMap.isUnit_iff_bijective]

/-- **Section 6.3** of [brezis2011functional], definition of the spectrum. Let $E$ be a Banach space
and $T \in \mathcal{L}(E)$. The spectrum is $\sigma(T) = \mathbb{R} \setminus \rho(T)$, so
$\lambda \in \sigma(T)$ if and only if $T - \lambda I$ is not bijective. -/
theorem mem_spectrum_iff_not_bijective [CompleteSpace E] (T : E →L[ℝ] E) (μ : ℝ) :
    μ ∈ spectrum ℝ T ↔ ¬ Function.Bijective (T - μ • (1 : E →L[ℝ] E)) := by
  rw [spectrum, Set.mem_compl_iff, mem_resolventSet_iff_bijective]

/-- **Section 6.3** of [brezis2011functional], definition of an eigenvalue. Let $E$ be a normed
space and $T \in \mathcal{L}(E)$. A real number $\lambda$ is an eigenvalue of $T$, written
$\lambda \in EV(T)$, if and only if $N(T - \lambda I) \neq \{0\}$.

The eigenspace $N(T - \lambda I)$ is Mathlib's `Module.End.eigenspace T λ`. -/
theorem hasEigenvalue_iff_ker_ne_bot (T : E →L[ℝ] E) (μ : ℝ) :
    HasEigenvalue (T : Module.End ℝ E) μ ↔ (T - μ • (1 : E →L[ℝ] E)).ker ≠ ⊥ := by
  have h : eigenspace (T : Module.End ℝ E) μ = (T - μ • (1 : E →L[ℝ] E)).ker := by
    ext x
    simp [LinearMap.mem_ker, sub_eq_zero]
  rw [hasEigenvalue_iff, h]

/-- Let $E$ be a Banach space, $T \in \mathcal{L}(E)$ and $\lambda \in \rho(T)$. Then
$T - \lambda I$ is an isomorphism of Banach spaces: there is a continuous linear equivalence
$E \to E$ equal to $T - \lambda I$, so $(T - \lambda I)^{-1} \in \mathcal{L}(E)$.

The source says that "it is useful to keep in mind that if $\lambda \in \rho(T)$ then
$(T - \lambda I)^{-1} \in \mathcal{L}(E)$ (see Corollary 2.7)". -/
theorem exists_equiv_of_mem_resolventSet [CompleteSpace E] (T : E →L[ℝ] E) {μ : ℝ}
    (h : μ ∈ resolventSet ℝ T) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = T - μ • (1 : E →L[ℝ] E) := by
  obtain ⟨hinj, hsurj⟩ := (mem_resolventSet_iff_bijective T μ).1 h
  exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- **Remark 6** in Chapter 6 of [brezis2011functional], first sentence. Let $E$ be a Banach space
and $T \in \mathcal{L}(E)$. Then $EV(T) \subseteq \sigma(T)$: every eigenvalue of $T$ lies in
the spectrum. -/
theorem remark_6_6 [CompleteSpace E] {T : E →L[ℝ] E} {μ : ℝ}
    (h : HasEigenvalue (T : Module.End ℝ E) μ) : μ ∈ spectrum ℝ T := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact h.mem_spectrum

/-! ### The right shift on $\ell^2$ -/

/-- **Remark 6** in Chapter 6 of [brezis2011functional], the right shift. The **right shift** on
$\ell^2$ is the operator
$$S_r u = (0, u_0, u_1, u_2, \dots),$$
that is, $(S_r u)_0 = 0$ and $(S_r u)_{n+1} = u_n$. It is a bounded operator, and an isometry.

The source writes $S_r u = (0, u_1, u_2, \dots)$ with indices from $1$. The definition is the
backbone's `lp.shiftRightL ℝ`. -/
def rightShift : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  lp.shiftRightL ℝ

/-- The right shift has the coordinate $(S_r u)_0 = 0$. -/
@[simp]
theorem rightShift_apply_zero (x : lp (fun _ : ℕ => ℝ) 2) : rightShift x 0 = 0 :=
  lp.shiftRightL_apply_zero ℝ x

/-- The right shift has the coordinates $(S_r u)_{n+1} = u_n$. -/
@[simp]
theorem rightShift_apply_succ (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    rightShift x (n + 1) = x n :=
  lp.shiftRightL_apply_succ ℝ x n

/-- The right shift is an isometry: $\|S_r u\| = \|u\|$ for every $u \in \ell^2$. -/
theorem norm_rightShift_apply (x : lp (fun _ : ℕ => ℝ) 2) : ‖rightShift x‖ = ‖x‖ :=
  lp.norm_shiftRightL_apply ℝ x

/-- **Remark 6** in Chapter 6 of [brezis2011functional], the right shift. For the right shift $S_r$
on $\ell^2$, $0 \in \sigma(S_r)$ but $0 \notin EV(S_r)$. So the inclusion
$EV(T) \subseteq \sigma(T)$ can be strict: here $N(S_r) = \{0\}$ and $R(S_r) \neq \ell^2$.

Equivalently, as Remark 5 of the source says, $S_r$ is injective but not surjective. -/
theorem remark_6_6_rightShift :
    (0 : ℝ) ∈ spectrum ℝ rightShift ∧
      ¬ HasEigenvalue (rightShift : Module.End ℝ (lp (fun _ : ℕ => ℝ) 2)) 0 := by
  have hinj : Function.Injective rightShift := fun x y hxy => by
    ext n
    have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z (n + 1)) hxy
    simpa using this
  constructor
  · rw [mem_spectrum_iff_not_bijective, zero_smul, sub_zero]
    rintro ⟨-, hsurj⟩
    obtain ⟨x, hx⟩ := hsurj (lp.single 2 0 1)
    have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z 0) hx
    simp at this
  · rw [hasEigenvalue_iff_ker_ne_bot, zero_smul, sub_zero, not_not, LinearMap.ker_eq_bot,
      ContinuousLinearMap.coe_coe]
    exact hinj

/-- **Remark 6** in Chapter 6 of [brezis2011functional], empty spectrum. Let $E$ be a Banach space
and let $T \in \mathcal{L}(E)$ satisfy $T^2 = -I$. Then $\sigma(T) = \emptyset$.

The source says that "it may happen that $EV(T) = \sigma(T) = \emptyset$". This statement is the
fact behind both of its examples: $(T - \lambda I)(T + \lambda I) = -(1 + \lambda^2) I$ is
invertible for every real $\lambda$. See also Exercise 6.16 of the source. -/
theorem remark_6_6_spectrum_eq_empty_of_sq_eq_neg_one [CompleteSpace E] {T : E →L[ℝ] E}
    (hT : T * T = -1) : spectrum ℝ T = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro μ hμ
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] at hμ
  refine hμ ⟨⟨μ • 1 - T, (μ ^ 2 + 1)⁻¹ • (μ • 1 + T), ?_, ?_⟩, rfl⟩
  · have h : (μ • (1 : E →L[ℝ] E) - T) * (μ • 1 + T) = (μ ^ 2 + 1) • 1 := by
      rw [sub_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        mul_smul_comm, one_mul, one_mul, mul_one, hT, smul_smul, add_smul, one_smul, ← sq]
      abel
    change (μ • 1 - T) * ((μ ^ 2 + 1)⁻¹ • (μ • 1 + T)) = 1
    rw [mul_smul_comm, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · have h : (μ • (1 : E →L[ℝ] E) + T) * (μ • 1 - T) = (μ ^ 2 + 1) • 1 := by
      rw [add_mul, mul_sub, mul_sub, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
        mul_smul_comm, one_mul, one_mul, mul_one, hT, smul_smul, add_smul, one_smul, ← sq]
      abel
    change ((μ ^ 2 + 1)⁻¹ • (μ • 1 + T)) * (μ • 1 - T) = 1
    rw [smul_mul_assoc, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- **Remark 6** in Chapter 6 of [brezis2011functional], the rotation. The rotation by $\pi/2$ of
$\mathbb{R}^2$, $R(x_0, x_1) = (-x_1, x_0)$, is a bounded operator with $\sigma(R) = \emptyset$,
and no real number is an eigenvalue of $R$.

The plane $\mathbb{R}^2$ is `EuclideanSpace ℝ (Fin 2)`. The second example of the source, the
operator $(u_1, u_2, u_3, u_4, \dots) \mapsto (-u_2, u_1, -u_4, u_3, \dots)$ on $\ell^2$,
satisfies $T^2 = -I$ and is covered by
`Brezis.Chapter06.remark_6_6_spectrum_eq_empty_of_sq_eq_neg_one`. -/
theorem remark_6_6_rotation :
    ∃ R : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      (∀ x, R x 0 = -x 1 ∧ R x 1 = x 0) ∧ spectrum ℝ R = ∅ ∧
        ∀ μ : ℝ, ¬ HasEigenvalue (R : Module.End ℝ (EuclideanSpace ℝ (Fin 2))) μ := by
  set R : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) !![0, -1; 1, 0] with hR
  have hsq : R * R = -1 := by
    rw [hR, ← map_mul, ← map_one (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2)), ← map_neg]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hspec := remark_6_6_spectrum_eq_empty_of_sq_eq_neg_one hsq
  refine ⟨R, fun x => ?_, hspec, fun μ hμ => ?_⟩
  · have hx : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
    rw [hR, hx, Matrix.toEuclideanCLM_toLp]
    constructor <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · have := remark_6_6 hμ
    rw [hspec] at this
    exact this

/-! ### Proposition 6.7 and Theorem 6.8 -/

/-- **Proposition 6.7** of [brezis2011functional], compactness. Let $E$ be a Banach space and
$T \in \mathcal{L}(E)$. Then the spectrum $\sigma(T)$ is compact.

In the source, $\rho(T)$ is open by the contraction mapping principle, and $\sigma(T)$ is
bounded. -/
theorem proposition_6_7 [CompleteSpace E] (T : E →L[ℝ] E) : IsCompact (spectrum ℝ T) :=
  spectrum.isCompact T

/-- **Proposition 6.7** of [brezis2011functional], the bound. Let $E$ be a Banach space and
$T \in \mathcal{L}(E)$. Then
$$\sigma(T) \subseteq [-\|T\|, +\|T\|].$$
-/
theorem proposition_6_7_subset [CompleteSpace E] (T : E →L[ℝ] E) :
    spectrum ℝ T ⊆ Set.Icc (-‖T‖) ‖T‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  · have := spectrum.subset_closedBall_norm (𝕜 := ℝ) T
    rwa [Real.closedBall_eq_Icc, zero_sub, zero_add] at this

/-- **Theorem 6.8(a)** of [brezis2011functional]. Let $E$ be an infinite-dimensional Banach space
and let $T \in \mathcal{K}(E)$. Then $0 \in \sigma(T)$. -/
theorem theorem_6_8_a [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T)
    (hE : ¬ FiniteDimensional ℝ E) : (0 : ℝ) ∈ spectrum ℝ T :=
  hT.zero_mem_spectrum hE

/-- **Theorem 6.8(b)** of [brezis2011functional]. Let $E$ be a Banach space and let
$T \in \mathcal{K}(E)$. Then
$$\sigma(T) \setminus \{0\} = EV(T) \setminus \{0\}.$$

**Generalization.** The source assumes that $E$ is infinite dimensional. This part holds without
that hypothesis.

The proof is Mathlib's Fredholm alternative `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`. -/
theorem theorem_6_8_b [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    spectrum ℝ T \ {0} = {μ | HasEigenvalue (T : Module.End ℝ E) μ} \ {0} := by
  ext μ
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hμ, hne⟩
    exact ⟨(hT.hasEigenvalue_iff_mem_spectrum hne).2 hμ, hne⟩
  · rintro ⟨hμ, hne⟩
    exact ⟨(hT.hasEigenvalue_iff_mem_spectrum hne).1 hμ, hne⟩

/-- **Theorem 6.8(c)** of [brezis2011functional]. Let $E$ be a Banach space and let
$T \in \mathcal{K}(E)$. Then one of the following holds: $\sigma(T) \setminus \{0\}$ is finite
(possibly empty), or there is an injective sequence $(\lambda_n)$ with $\{\lambda_n : n \in
\mathbb{N}\} = \sigma(T) \setminus \{0\}$ and $\lambda_n \to 0$.

**Generalization.** The source assumes that $E$ is infinite dimensional. This part is stated
without that hypothesis; in finite dimension the first alternative holds.

The source lists three cases: $\sigma(T) \setminus \{0\}$ is empty, finite, or a sequence that
tends to $0$. The first alternative here joins the first two. -/
theorem theorem_6_8_c [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    (spectrum ℝ T \ {0}).Finite ∨
      ∃ f : ℕ → ℝ, Function.Injective f ∧ Set.range f = spectrum ℝ T \ {0} ∧
        Tendsto f atTop (𝓝 0) :=
  hT.finite_or_exists_enumeration_spectrum

/-- **Lemma 6.2** of [brezis2011functional]. Let $E$ be a Banach space, let $T \in \mathcal{K}(E)$,
and let $(\lambda_n)$ be a sequence of distinct real numbers with
$\lambda_n \in \sigma(T) \setminus \{0\}$ for all $n$ and $\lambda_n \to \lambda$. Then
$\lambda = 0$. So every point of $\sigma(T) \setminus \{0\}$ is isolated.

The backbone proves a stronger form: every such sequence converges, and its limit is $0$. -/
theorem lemma_6_2 [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T) {l : ℕ → ℝ}
    (hl : Function.Injective l) (hmem : ∀ n, l n ∈ spectrum ℝ T \ {0}) {μ : ℝ}
    (hlim : Tendsto l atTop (𝓝 μ)) : μ = 0 := by
  have hev : ∀ n, HasEigenvalue (T : Module.End ℝ E) (l n) := fun n => by
    have := hmem n
    rw [theorem_6_8_b hT] at this
    exact this.1
  exact tendsto_nhds_unique hlim (hT.tendsto_zero_of_injective_of_forall_hasEigenvalue hl hev)

/-! ### The multiplication operators on $\ell^2$ -/

/-- **Remark 7** in Chapter 6 of [brezis2011functional], the multiplication operator. Let
$(\alpha_n)$ be a real sequence with $|\alpha_n| \le C$ for all $n$. The **multiplication
operator** on $\ell^2$ is the bounded operator
$$T u = (\alpha_0 u_0, \alpha_1 u_1, \alpha_2 u_2, \dots),$$
whose norm is at most $|C|$.

The source also uses this operator in Exercises 6.1 and 6.17, with indices from $1$. The
definition is the backbone's diagonal operator `lp.diagonalL`. -/
abbrev multiplicationOperator (α : ℕ → ℝ) {C : ℝ} (hα : ∀ n, |α n| ≤ C) :
    lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  lp.diagonalL (fun _ : ℕ => ℝ) 2 α hα

/-- The multiplication operator acts coordinatewise: $(T u)_n = \alpha_n u_n$. -/
theorem multiplicationOperator_apply (α : ℕ → ℝ) {C : ℝ} (hα : ∀ n, |α n| ≤ C)
    (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) : multiplicationOperator α hα x n = α n * x n :=
  rfl

/-- The truncated sequence $(\alpha_0, \dots, \alpha_{n-1}, 0, 0, \dots)$ is bounded by the bound
$C$ of $\alpha$. -/
private theorem abs_ite_lt_le {α : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |α n| ≤ C) (n k : ℕ) :
    |if k < n then α k else 0| ≤ C := by
  split_ifs
  · exact hC k
  · simpa using (abs_nonneg _).trans (hC 0)

/-- The truncated multiplication operator $T_n u = (\alpha_0 u_0, \dots, \alpha_{n-1} u_{n-1}, 0, 0,
\dots)$ has finite rank. -/
private theorem isFiniteRank_multiplicationOperator_truncation {α : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, |α n| ≤ C) (n : ℕ) :
    IsFiniteRank (multiplicationOperator (fun k => if k < n then α k else 0)
      (abs_ite_lt_le hC n)) :=
  lp.finiteDimensional_range_diagonalL _ _ (Finset.range n) fun _ hk =>
    ite_eq_right fun h => hk (Finset.mem_range.2 h)

/-- **Remark 7** in Chapter 6 of [brezis2011functional], compactness. Let $(\alpha_n)$ be a real
sequence with $\alpha_n \to 0$ and $|\alpha_n| \le C$ for all $n$. Then the multiplication
operator $T u = (\alpha_n u_n)_n$ on $\ell^2$ is compact.

The bound $C$ exists because a convergent sequence is bounded; it is an argument of
`Brezis.Chapter06.multiplicationOperator`. The proof shows that $T$ is the norm limit of the
truncations $T_n u = (\alpha_0 u_0, \dots, \alpha_{n-1} u_{n-1}, 0, 0, \dots)$, which have
finite rank, with $\|T_n - T\| \le \sup_{k \ge n} |\alpha_k| \to 0$. -/
theorem remark_6_7_isCompactOperator {α : ℕ → ℝ} (hα : Tendsto α atTop (𝓝 0)) {C : ℝ}
    (hC : ∀ n, |α n| ≤ C) : IsCompactOperator (multiplicationOperator α hC) := by
  refine corollary_6_2 (T := fun n =>
    multiplicationOperator (fun k => if k < n then α k else 0) (abs_ite_lt_le hC n))
    (fun n => isFiniteRank_multiplicationOperator_truncation hC n) ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hα (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le fun x => ?_
  have hle : ∀ k, ‖((multiplicationOperator (fun k => if k < n then α k else 0)
      (abs_ite_lt_le hC n) - multiplicationOperator α hC) x) k‖ ≤ ‖((ε / 2) • x) k‖ := by
    intro k
    rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      multiplicationOperator_apply, multiplicationOperator_apply, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_pos (half_pos hε)]
    split_ifs with hk
    · rw [sub_self, abs_zero]
      positivity
    · have h := hN k (by omega)
      rw [Real.dist_eq, sub_zero] at h
      rw [zero_mul, zero_sub, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_right h.le (abs_nonneg _)
  have h := lp.norm_mono two_ne_zero hle
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε)] at h

/-- **Remark 7** in Chapter 6 of [brezis2011functional], the spectrum. Let $(\alpha_n)$ be a real
sequence with $\alpha_n \to 0$ and $|\alpha_n| \le C$ for all $n$, and let $T$ be the
multiplication operator on $\ell^2$. Then
$$\sigma(T) = \{\alpha_n : n \in \mathbb{N}\} \cup \{0\},$$
every $\alpha_n$ is an eigenvalue of $T$, and $0$ is an eigenvalue of $T$ if and only if
$\alpha_n = 0$ for some $n$.

So $0$ may or may not belong to $EV(T)$. The eigenvector for $\alpha_n$ is the unit vector
$e_n$. The further claim of the source that $N(T)$ may be finite or infinite dimensional is not
stated. -/
theorem remark_6_7_spectrum {α : ℕ → ℝ} (hα : Tendsto α atTop (𝓝 0)) {C : ℝ}
    (hC : ∀ n, |α n| ≤ C) :
    spectrum ℝ (multiplicationOperator α hC) = Set.range α ∪ {0} ∧
      (∀ n, HasEigenvalue
        (multiplicationOperator α hC : Module.End ℝ (lp (fun _ : ℕ => ℝ) 2)) (α n)) ∧
      (HasEigenvalue (multiplicationOperator α hC : Module.End ℝ (lp (fun _ : ℕ => ℝ) 2)) 0 ↔
        ∃ n, α n = 0) := by
  have hev : ∀ n, HasEigenvalue
      (multiplicationOperator α hC : Module.End ℝ (lp (fun _ : ℕ => ℝ) 2)) (α n) := fun n => by
    refine hasEigenvalue_of_hasEigenvector (x := lp.single 2 n (1 : ℝ)) ⟨?_, ?_⟩
    · rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe]
      exact lp.diagonalL_single α hC n 1
    · intro h
      have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z n) h
      simp at this
  refine ⟨?_, hev, ?_⟩
  · refine Set.Subset.antisymm ?_ ?_
    · -- `μ ∉ range α ∪ {0}` is in the resolvent set: `T - μ I` has the bounded inverse
      -- given by multiplication with `(αₙ - μ)⁻¹`
      intro μ hμ
      by_contra hnot
      rw [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, not_or, not_exists] at hnot
      obtain ⟨hne, hμ0⟩ := hnot
      -- a uniform lower bound `δ` on `|αₙ - μ|`
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hα (|μ| / 2) (by positivity)
      have hpos : ∀ n, 0 < |α n - μ| := fun n => abs_pos.2 (sub_ne_zero.2 (hne n))
      obtain ⟨n₀, -, hn₀⟩ := (Finset.range (N + 1)).exists_min_image
        (fun n => if n < N then |α n - μ| else |μ| / 2) ⟨N, Finset.mem_range.2 N.lt_succ_self⟩
      have hδpos : 0 < if n₀ < N then |α n₀ - μ| else |μ| / 2 := by
        split_ifs
        · exact hpos n₀
        · positivity
      have hδle : ∀ n, (if n₀ < N then |α n₀ - μ| else |μ| / 2) ≤ |α n - μ| := fun n => by
        by_cases hn : n < N
        · have := hn₀ n (Finset.mem_range.2 (by omega))
          simpa only [hn, ite_true] using this
        · have h1 := hn₀ N (Finset.mem_range.2 N.lt_succ_self)
          simp only [lt_irrefl, ite_false] at h1
          have h2 := hN n (by omega)
          rw [Real.dist_eq, sub_zero] at h2
          have h3 : |μ| - |α n| ≤ |α n - μ| := by
            rw [abs_sub_comm]
            exact abs_sub_abs_le_abs_sub μ (α n)
          linarith
      have hinv : ∀ n, |(α n - μ)⁻¹| ≤ (if n₀ < N then |α n₀ - μ| else |μ| / 2)⁻¹ := fun n => by
        rw [abs_inv]
        exact inv_anti₀ hδpos (hδle n)
      -- the inverse of `T - μ I`
      have hcoord : ∀ x : lp (fun _ : ℕ => ℝ) 2, ∀ n,
          ((multiplicationOperator α hC - μ • 1) x) n = (α n - μ) * x n := fun x n => by
        rw [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
          Pi.smul_apply, multiplicationOperator_apply, smul_eq_mul]
        ring
      have hunit : IsUnit (multiplicationOperator α hC - μ • 1) := by
        refine ⟨⟨multiplicationOperator α hC - μ • 1,
          multiplicationOperator (fun n => (α n - μ)⁻¹) hinv, ?_, ?_⟩, rfl⟩
        · ext x n
          rw [mul_apply_eq_comp, hcoord, multiplicationOperator_apply, one_apply_eq_self]
          field_simp [sub_ne_zero.2 (hne n)]
        · ext x n
          rw [mul_apply_eq_comp, multiplicationOperator_apply, hcoord, one_apply_eq_self]
          field_simp [sub_ne_zero.2 (hne n)]
      rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub] at hμ
      exact hμ hunit.neg
    · rintro μ (⟨n, rfl⟩ | rfl)
      · exact remark_6_6 (hev n)
      · exact theorem_6_8_a (remark_6_7_isCompactOperator hα hC)
          lp.not_finiteDimensional_of_infinite
  · constructor
    · intro h
      obtain ⟨x, hx, hx0⟩ := h.exists_hasEigenvector
      rw [mem_eigenspace_iff, zero_smul] at hx
      by_contra hcontra
      push Not at hcontra
      refine hx0 ?_
      ext n
      have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z n) hx
      simp only [ContinuousLinearMap.coe_coe, multiplicationOperator_apply] at this
      change x n = 0
      exact (mul_eq_zero.1 this).resolve_left (hcontra n)
    · rintro ⟨n, hn⟩
      have := hev n
      rwa [hn] at this

/-! ### The ascent of $T - \lambda I$ -/

/-- The kernels of the powers of $T - \lambda I$ and of $\lambda I - T$ are equal. -/
private theorem ker_pow_sub_smul_one (T : E →L[ℝ] E) (μ : ℝ) (j : ℕ) :
    ((T - μ • (1 : E →L[ℝ] E)) ^ j).ker = ((μ • (1 : E →L[ℝ] E) - T) ^ j).ker := by
  rw [← neg_sub, neg_pow]
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.neg_one_pow, one_mul]
  · rw [hj.neg_one_pow, neg_one_mul, ContinuousLinearMap.toLinearMap_neg, LinearMap.ker_neg]

/-- **Comments on Chapter 6, item 3,** of [brezis2011functional], multiplicity of eigenvalues. Let
$E$ be a Banach space, let $T \in \mathcal{K}(E)$, and let
$\lambda \in \sigma(T) \setminus \{0\}$. Then there is an integer $p \ge 1$ such that
$$N((T - \lambda I)^j) \subsetneq N((T - \lambda I)^{j+1}) \quad \text{for } 0 \le j < p, \qquad
  N((T - \lambda I)^j) = N((T - \lambda I)^p) \quad \text{for } j \ge p,$$
and every $N((T - \lambda I)^j)$ is finite dimensional.

The integer $p$ is the ascent of $T - \lambda I$. It is at least $1$ because $\lambda$ is an
eigenvalue. -/
theorem ascent_stabilizes [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsCompactOperator T) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ T \ {0}) :
    ∃ p : ℕ, 1 ≤ p ∧
      (∀ j < p, ((T - μ • (1 : E →L[ℝ] E)) ^ j).ker <
        ((T - μ • (1 : E →L[ℝ] E)) ^ (j + 1)).ker) ∧
      (∀ j, p ≤ j → ((T - μ • (1 : E →L[ℝ] E)) ^ j).ker =
        ((T - μ • (1 : E →L[ℝ] E)) ^ p).ker) ∧
      ∀ j, FiniteDimensional ℝ ((T - μ • (1 : E →L[ℝ] E)) ^ j).ker := by
  have hne : μ ≠ 0 := hμ.2
  obtain ⟨ν, hstrict, hstab, -, -⟩ := hT.exists_riesz_index hne
  simp only [ker_pow_sub_smul_one]
  refine ⟨ν, ?_, hstrict, hstab, fun j => ?_⟩
  swap
  · rw [ker_pow_sub_smul_one]
    exact hT.finiteDimensional_ker_pow hne j
  by_contra hν
  have hev : HasEigenvalue (T : Module.End ℝ E) μ := by
    have := hμ
    rw [theorem_6_8_b hT] at this
    exact this.1
  rw [hasEigenvalue_iff_ker_ne_bot, ← pow_one (T - μ • 1), ker_pow_sub_smul_one,
    hstab 1 (by omega), ← hstab 0 (by omega), pow_zero] at hev
  exact hev (Submodule.eq_bot_iff _ |>.2 fun u hu => by simpa using hu)

end Brezis.Chapter06

end
