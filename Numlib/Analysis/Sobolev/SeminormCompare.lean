/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Domain.lean` and `Numlib/Analysis/Sobolev/MultiIndex.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.DenyLions

/-!
# The tensor Sobolev seminorm against the multi-index seminorm

Let $\Omega$ be an open subset of a finite-dimensional real normed space $E$, and let
$1 \le p \le \infty$. The module `Numlib.Analysis.Sobolev.Domain` measures the derivatives of order
$n$ of a function $f \in W^{k,p}(\Omega)$ by the $L^p(\Omega)$ norm $\|D^n f\|_{L^p(\Omega)}$ of the
operator norm of the weak derivative tensor $D^n f : \Omega \to \mathcal{L}^n(E; F)$
(`sobolevSeminorm`). The modules `Numlib.Analysis.Sobolev.MultiIndex` and
`Numlib.Analysis.Sobolev.DenyLions` index the derivatives by multi-indices $\alpha$ relative to a
basis $b = (e_i)_{i \in \iota}$ of $E$, and use the seminorm $|u|_{k,p,\Omega} =
\big(\sum_{|\alpha| = k} \|\partial^\alpha u\|_{L^p(\Omega)}^p\big)^{1/p}$
(`SobolevMultiIndex.topSeminorm`) of Definition 7.2.2 and §7.3.5 of [han2009theoretical]. On a
finite-dimensional space the two are equivalent: the operator norm of a symmetric tensor is
comparable to any norm on its finitely many entries. This module proves the two inequalities, with
constants that depend on the basis alone:
$$\|D^n u\|_{L^p(\Omega)} \le C_n \|u\|_{k,p,\Omega} \quad (n \le k), \qquad |u|_{k,p,\Omega} \le
  C'_k \|D^k u\|_{L^p(\Omega)}.$$
For the standard basis of $\mathbb{R}^N$ both constants are counts of multi-indices, $N^n$ and
$\#\{\alpha : |\alpha| = k\}$. The module also proves the algebra of the tensor seminorm on
$W^{k,p}(\Omega)$ that the finite element interpolation estimates of [han2009theoretical], §10.3,
use: finiteness, the triangle inequality, homogeneity, and the bound for a finite linear
combination.

## Main results

* `MemSobolev.sobolevSeminorm_ne_top`: the tensor seminorm of a function of $W^{k,p}(\Omega)$ is
  finite.
* `sobolevSeminorm_add_le`, `sobolevSeminorm_sub_le`, `sobolevSeminorm_const_smul`,
  `sobolevSeminorm_sum_smul_le`: the triangle inequality, homogeneity, and the bound for a finite
  linear combination.
* `MemSobolev.finsetSum`: $W^{k,p}(\Omega)$ is closed under finite sums.
* `MemSobolev.sobolevNorm_le_sum_sobolevSeminorm`: for $p < \infty$, the norm of $W^{k,p}(\Omega)$
  is at most the sum of the tensor seminorms of the orders $0, \dots, k$.
* `ContinuousMultilinearMap.norm_le_sum_norm_basisCoordProd_mul`: a continuous multilinear map is
  bounded by its values on tuples of basis vectors.
* `SobolevMultiIndex.weakDeriv_ae_eq_weakIteratedFDeriv_apply`: $\partial^\alpha u$ is the tensor
  derivative $D^{|\alpha|} u$ evaluated at the tuple of basis vectors that names $\alpha$.
* `SobolevMultiIndex.weakDeriv_multiIndexCount_ae_eq`: $D^n u$ evaluated at any tuple of basis
  vectors is the weak derivative $\partial^\alpha u$, where $\alpha$ counts how often each basis
  vector occurs.
* `SobolevMultiIndex.sobolevSeminorm_fn_le`: $\|D^n u\|_{L^p(\Omega)} \le C_n \|u\|_{k,p,\Omega}$
  for $n \le k$.
* `SobolevMultiIndex.ofReal_topSeminorm_le_sobolevSeminorm`,
  `SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm`: $|u|_{k,p,\Omega} \le C'_k \|D^k
  u\|_{L^p(\Omega)}$.

## Notation

* $D^n f$: the weak derivative of order $n$ of $f$ on $\Omega$, a function with values in the
  continuous $n$-linear maps from $E$ to $F$ (`weakIteratedFDeriv`). It is $0$ when $f$ has no such
  weak derivative.
* $\|u\|_{k,p,\Omega}$: the norm of $u$ in the multi-index space `SobolevMultiIndex F b k p Ω μ`.
* $e_\alpha$: the tuple of basis vectors that names the multi-index $\alpha$, of length $|\alpha|$
  (`multiIndexTuple`).

## Implementation notes

* The tensor seminorm `sobolevSeminorm f n p Ω μ` is an extended nonnegative real. The comparisons
  are stated in `ℝ≥0∞`, and `SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm` gives the
  real form.
-/

open Filter MeasureTheory Module Set TopologicalSpace

open scoped ENNReal NNReal

noncomputable section

/-! ### The algebra of the tensor seminorm on $W^{k,p}(\Omega)$ -/

section Algebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens E} {μ : Measure E} {k : ℕ} {p : ℝ≥0∞} {f g : E → F}

/-- Let $f \in W^{k,p}(\Omega)$. Then the tensor seminorm $\|D^k f\|_{L^p(\Omega)}$ is finite: it is
not $\infty$. -/
theorem MemSobolev.sobolevSeminorm_ne_top (hf : MemSobolev f k p Ω μ) :
    sobolevSeminorm f k p Ω μ ≠ ⊤ :=
  (hf.memLp_weakIteratedFDeriv le_rfl).eLpNorm_ne_top

/-- Let $f \in W^{k,p}(\Omega)$. Then the tensor seminorm satisfies
$\|D^k f\|_{L^p(\Omega)} < \infty$. -/
theorem MemSobolev.sobolevSeminorm_lt_top (hf : MemSobolev f k p Ω μ) :
    sobolevSeminorm f k p Ω μ < ⊤ :=
  lt_top_iff_ne_top.2 hf.sobolevSeminorm_ne_top

/-- The **triangle inequality for the tensor Sobolev seminorm**. Let $1 \le p$, and let
$f, g \in W^{k,p}(\Omega)$. Then
$$\|D^k (f + g)\|_{L^p(\Omega)} \le \|D^k f\|_{L^p(\Omega)} + \|D^k g\|_{L^p(\Omega)}.$$
-/
theorem sobolevSeminorm_add_le (hp : 1 ≤ p) (hf : MemSobolev f k p Ω μ)
    (hg : MemSobolev g k p Ω μ) :
    sobolevSeminorm (f + g) k p Ω μ ≤ sobolevSeminorm f k p Ω μ + sobolevSeminorm g k p Ω μ := by
  have hw := (hf.hasWeakIteratedFDerivOn le_rfl).add (hg.hasWeakIteratedFDerivOn le_rfl)
  unfold sobolevSeminorm
  rw [hw.eLpNorm_weakIteratedFDeriv]
  exact eLpNorm_add_le_of_norm hp

/-- The **triangle inequality for the tensor Sobolev seminorm of a difference**. Let $1 \le p$, and
let $f, g \in W^{k,p}(\Omega)$. Then
$$\|D^k (f - g)\|_{L^p(\Omega)} \le \|D^k f\|_{L^p(\Omega)} + \|D^k g\|_{L^p(\Omega)}.$$
-/
theorem sobolevSeminorm_sub_le (hp : 1 ≤ p) (hf : MemSobolev f k p Ω μ)
    (hg : MemSobolev g k p Ω μ) :
    sobolevSeminorm (f - g) k p Ω μ ≤ sobolevSeminorm f k p Ω μ + sobolevSeminorm g k p Ω μ := by
  have hw := (hf.hasWeakIteratedFDerivOn le_rfl).sub (hg.hasWeakIteratedFDerivOn le_rfl)
  unfold sobolevSeminorm
  rw [hw.eLpNorm_weakIteratedFDeriv]
  exact eLpNorm_sub_le_of_norm hp

/-- **Homogeneity of the tensor Sobolev seminorm**. Let $f \in W^{k,p}(\Omega)$ and
$c \in \mathbb{R}$. Then $\|D^k (c f)\|_{L^p(\Omega)} = |c| \, \|D^k f\|_{L^p(\Omega)}$. -/
theorem sobolevSeminorm_const_smul (hf : MemSobolev f k p Ω μ) (c : ℝ) :
    sobolevSeminorm (c • f) k p Ω μ = ‖c‖ₑ * sobolevSeminorm f k p Ω μ := by
  have hw := (hf.hasWeakIteratedFDerivOn le_rfl).const_smul c
  unfold sobolevSeminorm
  rw [hw.eLpNorm_weakIteratedFDeriv, eLpNorm_const_smul]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- Let $s$ be a finite set of indices and let $f_i \in W^{k,p}(\Omega)$ for every $i \in s$. Then
$\sum_{i \in s} f_i \in W^{k,p}(\Omega)$.

This result needs neither finite dimension of $E$ nor completeness of $F$; it needs only that
the open sets of $E$ are measurable. -/
theorem MemSobolev.finsetSum [OpensMeasurableSpace E] {ι : Type*} {s : Finset ι} {f : ι → E → F}
    (hf : ∀ i ∈ s, MemSobolev (f i) k p Ω μ) : MemSobolev (∑ i ∈ s, f i) k p Ω μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using memSobolev_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- The **tensor Sobolev seminorm of a finite linear combination**. Let $1 \le p$, let $s$ be a
finite set of indices, let $f_i \in W^{k,p}(\Omega)$ for every $i \in s$, and let
$c_i \in \mathbb{R}$. Then
$$\Big\|D^k \sum_{i \in s} c_i f_i\Big\|_{L^p(\Omega)} \le \sum_{i \in s} |c_i| \, \|D^k
  f_i\|_{L^p(\Omega)}.$$
-/
theorem sobolevSeminorm_sum_smul_le (hp : 1 ≤ p) {ι : Type*} {s : Finset ι} {f : ι → E → F}
    (hf : ∀ i ∈ s, MemSobolev (f i) k p Ω μ) (c : ι → ℝ) :
    sobolevSeminorm (∑ i ∈ s, c i • f i) k p Ω μ
      ≤ ∑ i ∈ s, ‖c i‖ₑ * sobolevSeminorm (f i) k p Ω μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hw : HasWeakIteratedFDerivOn k (0 : E → F) 0 Ω μ := HasWeakIteratedFDerivOn.zero
    unfold sobolevSeminorm
    rw [hw.eLpNorm_weakIteratedFDeriv, eLpNorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hmem : MemSobolev (∑ i ∈ s, c i • f i) k p Ω μ :=
      MemSobolev.finsetSum fun i hi ↦ (hf i (Finset.mem_insert_of_mem hi)).const_smul (c i)
    refine (sobolevSeminorm_add_le hp ((hf a (Finset.mem_insert_self a s)).const_smul (c a))
      hmem).trans ?_
    rw [sobolevSeminorm_const_smul (hf a (Finset.mem_insert_self a s))]
    exact add_le_add le_rfl (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- The **Sobolev norm is at most the sum of the seminorms of all orders**. Let $1 \le p < \infty$
and $f \in W^{k,p}(\Omega)$. Then
$$\|f\|_{k,p,\Omega} = \Big(\sum_{n = 0}^{k} \|D^n f\|_{L^p(\Omega)}^p\Big)^{1/p} \le \sum_{n =
  0}^{k} \|D^n f\|_{L^p(\Omega)}.$$

Here $\|f\|_{k,p,\Omega}$ is `sobolevNorm`. The inequality is the bound of the $\ell^p$ norm by
the $\ell^1$ norm, `Real.rpow_sum_rpow_le_sum`. -/
theorem MemSobolev.sobolevNorm_le_sum_sobolevSeminorm [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hf : MemSobolev f k p Ω μ) :
    sobolevNorm f k p Ω μ ≤ ∑ n : Fin (k + 1), sobolevSeminorm f n p Ω μ := by
  have hfin : ∀ n : Fin (k + 1), sobolevSeminorm f n p Ω μ ≠ ⊤ := fun n ↦
    (hf.mono_order (by exact_mod_cast Nat.lt_succ_iff.1 n.2)).sobolevSeminorm_ne_top
  have hP : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have key : ∀ n : Fin (k + 1), eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict (Ω : Set E))
      = ENNReal.ofReal (sobolevSeminorm f n p Ω μ).toReal := fun n ↦
    (ENNReal.ofReal_toReal (hfin n)).symm
  simp only [sobolevNorm, hp, ↓reduceIte]
  simp_rw [key]
  calc (∑ n : Fin (k + 1), ENNReal.ofReal (sobolevSeminorm f n p Ω μ).toReal ^ p.toReal)
        ^ (1 / p.toReal)
      = ENNReal.ofReal ((∑ n : Fin (k + 1), (sobolevSeminorm f n p Ω μ).toReal ^ p.toReal)
          ^ (1 / p.toReal)) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)
          (by positivity), ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
        congr 1
        exact Finset.sum_congr rfl fun n _ ↦
          ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hP
    _ ≤ ENNReal.ofReal (∑ n : Fin (k + 1), (sobolevSeminorm f n p Ω μ).toReal) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_sum_rpow_le_sum (fun _ ↦ ENNReal.toReal_nonneg) hp)
    _ = ∑ n : Fin (k + 1), sobolevSeminorm f n p Ω μ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg]
        exact Finset.sum_congr rfl fun n _ ↦ ENNReal.ofReal_toReal (hfin n)

end Algebra

/-! ### A continuous multilinear map is bounded by its values on tuples of basis vectors -/

section Multilinear

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {ι : Type*} [Fintype ι]

/-- **A continuous multilinear map is bounded by its values on tuples of basis vectors**. Let
$b = (e_i)_{i \in \iota}$ be a finite basis of $E$, and let $T : E^n \to G$ be a continuous
$n$-linear map. Then
$$\|T\| \le \sum_{m : \{0, \dots, n-1\} \to \iota} \|\pi_m\| \, \|T(e_{m(0)}, \dots,
  e_{m(n-1)})\|,$$
where $\pi_m(y_0, \dots, y_{n-1}) = \prod_j b^*_{m(j)}(y_j)$ is the product of the coordinate
functionals named by $m$ (`basisCoordProd b m`).

The proof expands $T$ in the basis with `ContinuousMultilinearMap.apply_eq_sum_basis`. -/
theorem ContinuousMultilinearMap.norm_le_sum_norm_basisCoordProd_mul (b : Basis ι ℝ E) {n : ℕ}
    (T : E [×n]→L[ℝ] G) :
    ‖T‖ ≤ ∑ m : Fin n → ι, ‖basisCoordProd b m‖ * ‖T fun j ↦ b (m j)‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun y ↦ ?_
  rw [ContinuousMultilinearMap.apply_eq_sum_basis b T y, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [norm_smul, ← basisCoordProd_apply, mul_assoc, mul_comm ‖T fun j ↦ b (m j)‖,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right ((basisCoordProd b m).le_opNorm y) (norm_nonneg _)

end Multilinear

/-! ### The comparison of the two seminorms -/

section Compare

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E} {μ : Measure E}

namespace SobolevMultiIndex

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] in
/-- Let $u$ be an element of the multi-index space $W^{k,p}(\Omega)$. Then its function
`SobolevMultiIndex.fn u` lies in $W^{k,p}(\Omega)$ in the tensor formulation: it satisfies
`MemSobolev`. -/
theorem memSobolev_fn (u : SobolevMultiIndex F b k p Ω μ) : MemSobolev (fn u) k p Ω μ :=
  (memSobolevMultiIndex u).memSobolev

omit [Fact (1 ≤ p)] in
/-- **$\partial^\alpha u$ is the tensor derivative of order $|\alpha|$ at the tuple that names
$\alpha$.** Let $u$ be an element of the multi-index space $W^{k,p}(\Omega)$ for a basis $b$ of
$E$, and let $|\alpha| \le k$. Then, for almost every $x \in \Omega$,
$$\partial^\alpha u(x) = D^{|\alpha|} u(x)(e_\alpha),$$
where $e_\alpha$ is the tuple of basis vectors that names $\alpha$ (`multiIndexTuple`). -/
theorem weakDeriv_ae_eq_weakIteratedFDeriv_apply (u : SobolevMultiIndex F b k p Ω μ)
    (α : MultiIndexLE ι k) :
    (weakDeriv u α : E → F) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ weakIteratedFDeriv (∑ i, α.1 i) (fn u) Ω μ x (multiIndexTuple (b : ι → E) α.1) := by
  have h1 := hasWeakIteratedLineDerivOn u α
  have h2 := ((memSobolev_fn u).hasWeakIteratedFDerivOn α.2).lineDeriv
    (multiIndexTuple (b : ι → E) α.1)
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)

omit [Fact (1 ≤ p)] in
/-- **The tensor derivative at a tuple of basis vectors is a weak derivative $\partial^\alpha u$.**
Let $u$ be an element of the multi-index space $W^{k,p}(\Omega)$ for a basis
$b = (e_i)_{i \in \iota}$ of $E$, let $n \le k$, and let $m : \{0, \dots, n-1\} \to \iota$. Let
$\alpha$ be the multi-index that counts how often each index occurs in $m$ (`multiIndexCount`).
Then, for almost every $x \in \Omega$,
$$\partial^\alpha u(x) = D^n u(x)(e_{m(0)}, \dots, e_{m(n-1)}).$$

The proof uses the symmetry of the weak derivative in its directions. -/
theorem weakDeriv_multiIndexCount_ae_eq (u : SobolevMultiIndex F b k p Ω μ) {n : ℕ} (hn : n ≤ k)
    (m : Fin n → ι) :
    (weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ : E → F)
      =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ weakIteratedFDeriv n (fn u) Ω μ x fun j ↦ b (m j) := by
  have hperm : (List.ofFn (multiIndexTuple (b : ι → E) (multiIndexCount m))).Perm
      (List.ofFn fun j ↦ b (m j)) := by
    rw [← multiIndexDirections_eq_ofFn]
    exact (multiIndexDirections_multiIndexCount_perm (b : ι → E) m).symm
  have h1 := (hasWeakIteratedLineDerivOn u ⟨multiIndexCount m,
    (sum_multiIndexCount m).le.trans hn⟩).of_perm hperm
  have h2 := ((memSobolev_fn u).hasWeakIteratedFDerivOn hn).lineDeriv fun j ↦ b (m j)
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fact (1 ≤ p)] in
/-- For an element $u$ of the multi-index space $W^{k,p}(\Omega)$ and $|\alpha| \le k$, the
$L^p(\Omega)$ norm of $\partial^\alpha u$ as an extended real (`eLpNorm`) is its norm in
$L^p(\Omega)$. -/
theorem eLpNorm_weakDeriv (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    eLpNorm (weakDeriv u α) p (μ.restrict (Ω : Set E)) = ENNReal.ofReal ‖weakDeriv u α‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

/-- **The tensor seminorm is bounded by the multi-index norm.** Let $u$ be an element of the
multi-index space $W^{k,p}(\Omega)$ for a basis $b = (e_i)_{i \in \iota}$ of $E$, and let
$n \le k$. Then
$$\|D^n u\|_{L^p(\Omega)} \le \Big(\sum_{m : \{0, \dots, n-1\} \to \iota} \|\pi_m\|\Big)
  \|u\|_{k,p,\Omega},$$
where $\pi_m$ is the product of the coordinate functionals named by $m$ (`basisCoordProd b m`).

The tensor $D^n u(x)$ is bounded by its values on tuples of basis vectors
(`ContinuousMultilinearMap.norm_le_sum_norm_basisCoordProd_mul`). These values are the
$\partial^\alpha u(x)$ (`SobolevMultiIndex.weakDeriv_multiIndexCount_ae_eq`), and each of them
has $L^p(\Omega)$ norm at most $\|u\|_{k,p,\Omega}$. -/
theorem sobolevSeminorm_fn_le (u : SobolevMultiIndex F b k p Ω μ) {n : ℕ} (hn : n ≤ k) :
    sobolevSeminorm (fn u) n p Ω μ
      ≤ ENNReal.ofReal (∑ m : Fin n → ι, ‖basisCoordProd b m‖) * ENNReal.ofReal ‖u‖ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hae : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖weakIteratedFDeriv n (fn u) Ω μ x‖
      ≤ ∑ m : Fin n → ι, ‖basisCoordProd b m‖
        * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖ := by
    filter_upwards [ae_all_iff.2 fun m : Fin n → ι ↦ weakDeriv_multiIndexCount_ae_eq u hn m]
      with x hx
    refine (ContinuousMultilinearMap.norm_le_sum_norm_basisCoordProd_mul b _).trans
      (Finset.sum_le_sum fun m _ ↦ ?_)
    rw [hx m]
  calc sobolevSeminorm (fn u) n p Ω μ
      ≤ eLpNorm (fun x ↦ ∑ m : Fin n → ι, ‖basisCoordProd b m‖
          * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖) p
          (μ.restrict (Ω : Set E)) :=
        eLpNorm_mono_ae_real ((memSobolev_fn u).memLp_weakIteratedFDeriv hn).aestronglyMeasurable
          hae
    _ ≤ ∑ m : Fin n → ι, eLpNorm (fun x ↦ ‖basisCoordProd b m‖
          * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖) p
          (μ.restrict (Ω : Set E)) := by
        have heq : (fun x ↦ ∑ m : Fin n → ι, ‖basisCoordProd b m‖
            * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖)
            = ∑ m : Fin n → ι, fun x ↦ ‖basisCoordProd b m‖
              * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖ := by
          funext x
          simp
        rw [heq]
        exact eLpNorm_sum_le_of_norm hp
    _ ≤ ∑ m : Fin n → ι, ENNReal.ofReal ‖basisCoordProd b m‖ * ENNReal.ofReal ‖u‖ := by
        refine Finset.sum_le_sum fun m _ ↦ ?_
        have hsmul : (fun x ↦ ‖basisCoordProd b m‖
            * ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖)
            = ‖basisCoordProd b m‖ • fun x ↦
              ‖weakDeriv u ⟨multiIndexCount m, (sum_multiIndexCount m).le.trans hn⟩ x‖ := by
          funext x
          simp
        rw [hsmul, eLpNorm_const_smul, Real.enorm_of_nonneg (norm_nonneg _),
          eLpNorm_norm _ (Lp.memLp _).aestronglyMeasurable, eLpNorm_weakDeriv]
        gcongr
        exact norm_weakDeriv_le u _
    _ = ENNReal.ofReal (∑ m : Fin n → ι, ‖basisCoordProd b m‖) * ENNReal.ofReal ‖u‖ := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _]

/-- **The multi-index seminorm is bounded by the tensor seminorm.** Let $u$ be an element of the
multi-index space $W^{k,p}(\Omega)$ for a basis $b$ of $E$. Then
$$|u|_{k,p,\Omega} \le \Big(\sum_{|\alpha| = k} \prod_j \|(e_\alpha)_j\|\Big) \|D^k
  u\|_{L^p(\Omega)},$$
where $e_\alpha$ is the tuple of basis vectors that names $\alpha$, and $|u|_{k,p,\Omega}$ is
`SobolevMultiIndex.topSeminorm`.

The proof bounds $|u|_{k,p,\Omega}$ by $\sum_{|\alpha| = k} \|\partial^\alpha u\|_{L^p(\Omega)}$
(`PiLp.norm_le_sum_norm`), and $\partial^\alpha u(x) = D^k u(x)(e_\alpha)$ has norm at most
$\|D^k u(x)\| \prod_j \|(e_\alpha)_j\|$. -/
theorem ofReal_topSeminorm_le_sobolevSeminorm (u : SobolevMultiIndex F b k p Ω μ) :
    ENNReal.ofReal (topSeminorm F b k p Ω μ u)
      ≤ ENNReal.ofReal (∑ α : MultiIndexEq ι k, ∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
        * sobolevSeminorm (fn u) k p Ω μ := by
  have hterm : ∀ α : MultiIndexEq ι k, ENNReal.ofReal ‖weakDeriv u α.1‖
      ≤ ENNReal.ofReal (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
        * sobolevSeminorm (fn u) k p Ω μ := by
    intro α
    rw [← eLpNorm_weakDeriv,
      eLpNorm_congr_ae (weakDeriv_ae_eq_weakIteratedFDeriv_apply u α.1)]
    have hae : ∀ᵐ x ∂μ.restrict (Ω : Set E),
        ‖weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x (multiIndexTuple (b : ι → E) α.1.1)‖
          ≤ (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
            * ‖weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x‖ :=
      Eventually.of_forall fun x ↦ by
        rw [mul_comm]
        exact ContinuousMultilinearMap.le_opNorm _ _
    have hmeas : AEStronglyMeasurable (fun x ↦ weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x
        (multiIndexTuple (b : ι → E) α.1.1)) (μ.restrict (Ω : Set E)) :=
      ((ContinuousMultilinearMap.apply ℝ (fun _ ↦ E) F
        (multiIndexTuple (b : ι → E) α.1.1)).comp_memLp'
        ((memSobolev_fn u).memLp_weakIteratedFDeriv α.1.2)).aestronglyMeasurable
    refine (eLpNorm_mono_ae_real hmeas hae).trans (le_of_eq ?_)
    have hsmul : (fun x ↦ (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
        * ‖weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x‖)
        = (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
          • fun x ↦ ‖weakIteratedFDeriv (∑ i, α.1.1 i) (fn u) Ω μ x‖ := by
      funext x
      simp
    rw [hsmul, eLpNorm_const_smul,
      Real.enorm_of_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)]
    have key : ∀ n, n = k → eLpNorm (fun x ↦ ‖weakIteratedFDeriv n (fn u) Ω μ x‖) p
        (μ.restrict (Ω : Set E)) = sobolevSeminorm (fn u) k p Ω μ := by
      rintro n rfl
      exact eLpNorm_norm _
        ((memSobolev_fn u).memLp_weakIteratedFDeriv le_rfl).aestronglyMeasurable
    rw [key _ α.2]
  calc ENNReal.ofReal (topSeminorm F b k p Ω μ u)
      ≤ ENNReal.ofReal (∑ α : MultiIndexEq ι k, ‖weakDeriv u α.1‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [topSeminorm_apply, topDeriv]
        exact PiLp.norm_le_sum_norm _
    _ = ∑ α : MultiIndexEq ι k, ENNReal.ofReal ‖weakDeriv u α.1‖ :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ ∑ α : MultiIndexEq ι k, ENNReal.ofReal (∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
          * sobolevSeminorm (fn u) k p Ω μ := Finset.sum_le_sum fun α _ ↦ hterm α
    _ = _ := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun _ _ ↦
          Finset.prod_nonneg fun _ _ ↦ norm_nonneg _]

/-- The real form of `SobolevMultiIndex.ofReal_topSeminorm_le_sobolevSeminorm`. Let $u$ be an
element of the multi-index space $W^{k,p}(\Omega)$ for a basis $b$ of $E$. Then
$$|u|_{k,p,\Omega} \le \Big(\sum_{|\alpha| = k} \prod_j \|(e_\alpha)_j\|\Big) \|D^k
  u\|_{L^p(\Omega)},$$
where the tensor seminorm on the right is converted to a real number. That number is finite. -/
theorem topSeminorm_le_mul_toReal_sobolevSeminorm (u : SobolevMultiIndex F b k p Ω μ) :
    topSeminorm F b k p Ω μ u
      ≤ (∑ α : MultiIndexEq ι k, ∏ j, ‖multiIndexTuple (b : ι → E) α.1.1 j‖)
        * (sobolevSeminorm (fn u) k p Ω μ).toReal := by
  have hfin : sobolevSeminorm (fn u) k p Ω μ ≠ ⊤ := (memSobolev_fn u).sobolevSeminorm_ne_top
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    (ofReal_topSeminorm_le_sobolevSeminorm u)
  rwa [ENNReal.toReal_ofReal (apply_nonneg _ _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at h

end SobolevMultiIndex

end Compare

end
