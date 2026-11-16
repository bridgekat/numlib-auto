/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.HermiteGenocchi
import Numlib.Analysis.Matrix.Function.Triangular
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Analytic
import Numlib.Approximation.CompositeQuadrature

/-!
# How well $g(A)$ approximates $f(A)$

Let $A$ be a complex square matrix, and let $f$ and $g$ be functions that are analytic near the
spectrum of $A$. This file bounds $\|f(A) - g(A)\|$ by $f - g$ and its derivatives near the
spectrum, following [golub2013matrix], §9.2. The Jordan bound (Theorem 9.2.1 of [golub2013matrix])
uses a Jordan form $P^{-1} A P$ and bounds the spectral norm by $\|P\|_2 \|P^{-1}\|_2$ times the
largest weighted derivative of $f - g$ at the eigenvalues. The Schur bound (Theorem 9.2.2 of
[golub2013matrix]) uses a Schur form $Q^H A Q = \operatorname{diag}(T) + N$ with $N$ strictly upper
triangular, and gives
$$\|f(A) - g(A)\|_F \le \sum_{r=0}^{n-1} \delta_r \frac{\| |N|^r \|_F}{r!}$$
when $\|(f - g)^{(r)}\| \le \delta_r$ on a convex set that contains the spectrum. The file also
bounds the error of the composite Simpson rule for $\int_a^b f(tA) \, dt$.

The Taylor truncation bound, Theorem 9.2.3 of [golub2013matrix], holds in every complete normed
algebra and is `norm_pfc_sub_sum_le` in
`Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Analytic`.

## Main results

* `Matrix.l2_opNorm_pfc_jordanBlock_le`: if $|h^{(r)}(\mu)| / r! \le M$ for $r < k$, then
  $\|h(J_k(\mu))\|_2 \le kM$.
* `Matrix.l2_opNorm_pfc_sub_le_of_conj_jordanForm`: the Jordan bound, Theorem 9.2.1 of
  [golub2013matrix].
* `Matrix.frobenius_norm_pfc_sub_le` and `Matrix.frobenius_norm_pfc_sub_le_of_isCompact`: the Schur
  bound, Theorem 9.2.2 of [golub2013matrix], with given bounds $\delta_r$ and with suprema on a
  compact set.
* `Matrix.norm_integral_pfc_smul_sub_simpsonSum_le`: the error of the composite Simpson rule for
  $\int_a^b f(tA) \, dt$, (9.2.7) of [golub2013matrix] with the missing factor $A^4$.

## Proof outline

For the Jordan bound, $f(A) - g(A) = (f - g)(A) = P \operatorname{diag}((f - g)(J_i)) P^{-1}$, and
each Jordan block is bounded entrywise. For the Schur bound, the unitary invariance of the Frobenius
norm reduces the bound to the triangular matrix $T$. The entries of $h(T)$ are sums of divided
differences of $h$ along paths of the strictly upper triangular part (Theorem 9.1.4 of
[golub2013matrix]), and the Hermite–Genocchi formula bounds the divided differences by the
derivatives of $h$.

## Implementation notes

* The spectral norm is Mathlib's scoped `Matrix.Norms.L2Operator`, and the Frobenius norm is the
  scoped `Matrix.Norms.Frobenius`.
* The bounds on the derivatives are hypotheses $\delta_r \ge \|\dots\|$, so the main statements need
  no compactness. The suprema of [golub2013matrix] appear only in the form on a compact set.
-/

open Polynomial Hermite

namespace Matrix

section Jordan

open scoped Matrix.Norms.L2Operator

/-- **The spectral norm of a function of a Jordan block.** Let $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, let $h : \mathbb{K} \to \mathbb{K}$, let $\mu \in \mathbb{K}$ and
$k \in \mathbb{N}$, and let $M \ge 0$ with
$$\frac{|h^{(r)}(\mu)|}{r!} \le M \qquad \text{for all } r < k.$$
Then $\|h(J_k(\mu))\|_2 \le kM$. This is the inner step of the proof of Theorem 9.2.1 of
[golub2013matrix] ("using Theorem 9.1.2 and (2.3.8)").

The entries of $h(J_k(\mu))$ are $h^{(j-i)}(\mu) / (j - i)!$ (`Matrix.pfc_jordanBlock_apply`),
and a $k \times k$ matrix with entries bounded by $M$ has spectral norm at most $kM$. -/
theorem l2_opNorm_pfc_jordanBlock_le {𝕜 : Type*} [RCLike 𝕜] (h : 𝕜 → 𝕜) (k : ℕ) (μ : 𝕜)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ r < k, ‖iteratedDeriv r h μ‖ / r.factorial ≤ M) :
    ‖pfc h (jordanBlock k μ)‖ ≤ k * M := by
  have := l2_opNorm_le_sqrt_card_mul_of_forall_norm_le (pfc h (jordanBlock k μ)) hM0
    fun i j => by
      rw [pfc_jordanBlock_apply]
      split_ifs with hij
      · rw [taylorJet, norm_div, RCLike.norm_natCast]
        exact hM _ (by omega)
      · rw [norm_zero]
        exact hM0
  rwa [lpOpNorm_two, Fintype.card_fin, Real.sqrt_mul_self (Nat.cast_nonneg _)] at this

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If $P^{-1} A P$ is a Jordan form of $A$ and the block $i$ is not empty, the eigenvalue $\mu_i$
of the block lies in the spectrum of $A$. -/
private theorem mem_spectrum_of_conj_jordanForm {ι : Type*} [Finite ι] [DecidableEq ι]
    {e : ι → ℕ} {μ : ι → ℂ} (σ : (Σ i, Fin (e i)) ≃ n) {A P : Matrix n n ℂ} (hP : IsUnit P)
    (h : P⁻¹ * A * P = reindex σ σ (jordanForm e μ)) {i : ι} (hi : 0 < e i) :
    μ i ∈ spectrum ℂ A := by
  have := Fintype.ofFinite ι
  have hdet := (isUnit_iff_isUnit_det P).mp hP
  have hc : A.charpoly = ∏ j, (X - C (μ j)) ^ e j := by
    rw [← charpoly_jordanForm, ← charpoly_reindex σ, ← h, Matrix.mul_assoc, charpoly_mul_comm,
      Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.mul_one]
  refine mem_spectrum_of_isRoot_charpoly ?_
  rw [IsRoot, hc, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [zero_pow hi.ne'])

/-- **The Jordan bound.** Let $A, P \in \mathbb{C}^{n \times n}$ with $P$ invertible, and let
$P^{-1} A P = \operatorname{diag}(J_{e_1}(\mu_1), \dots, J_{e_s}(\mu_s))$ be a Jordan form of
$A$. Let $f, g : \mathbb{C} \to \mathbb{C}$ be analytic at every eigenvalue of $A$, and let
$M \ge 0$ with
$$e_i \, \frac{|f^{(r)}(\mu_i) - g^{(r)}(\mu_i)|}{r!} \le M \qquad \text{for all } i \text{ and
  all } r < e_i.$$
Then
$$\|f(A) - g(A)\|_2 \le \|P\|_2 \, \|P^{-1}\|_2 \, M.$$
This is Theorem 9.2.1 of [golub2013matrix], where $\|P\|_2 \|P^{-1}\|_2$ is the condition number
$\kappa_2(X)$ and $M$ is the maximum over $i$ and $r$.

The Jordan form is `Matrix.jordanForm e μ` with rows and columns renumbered by a bijection `σ`.
The proof writes $f(A) - g(A) = (f - g)(A) = P \operatorname{diag}((f - g)(J_{e_i}(\mu_i)))
P^{-1}$ (`Matrix.pfc_conj_jordanForm`). The norm of the block diagonal matrix is the largest
norm of a block (`Matrix.l2_opNorm_blockDiagonal'`), and each block is bounded by
`Matrix.l2_opNorm_pfc_jordanBlock_le`. -/
theorem l2_opNorm_pfc_sub_le_of_conj_jordanForm {ι : Type*} [Finite ι] [DecidableEq ι]
    {e : ι → ℕ} {μ : ι → ℂ} (σ : (Σ i, Fin (e i)) ≃ n) {A P : Matrix n n ℂ} (hP : IsUnit P)
    (h : P⁻¹ * A * P = reindex σ σ (jordanForm e μ)) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z) (hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ g z)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, ∀ r < e i,
      (e i : ℝ) * (‖iteratedDeriv r f (μ i) - iteratedDeriv r g (μ i)‖ / r.factorial) ≤ M) :
    ‖pfc f A - pfc g A‖ ≤ ‖P‖ * ‖P⁻¹‖ * M := by
  have := Fintype.ofFinite ι
  have hroot : ∀ z ∈ (minpoly ℂ A).roots, z ∈ spectrum ℂ A := fun z hz =>
    spectrum.mem_of_mem_roots_minpoly hz
  rw [← pfc_sub (fun z hz => (hf z (hroot z hz)).contDiffAt)
    (fun z hz => (hg z (hroot z hz)).contDiffAt), pfc_conj_jordanForm σ hP h]
  have hblock : ‖blockDiagonal' fun i => pfc (f - g) (jordanBlock (e i) (μ i))‖ ≤ M := by
    rw [l2_opNorm_blockDiagonal']
    refine Real.iSup_le (fun i => ?_) hM0
    rcases Nat.eq_zero_or_pos (e i) with he | he
    · have : pfc (f - g) (jordanBlock (e i) (μ i)) = 0 := by
        ext a
        exact absurd a.isLt (by omega)
      rw [this, norm_zero]
      exact hM0
    · have hμ := mem_spectrum_of_conj_jordanForm σ hP h he
      have hbound := l2_opNorm_pfc_jordanBlock_le (f - g) (e i) (μ i)
        (div_nonneg hM0 (Nat.cast_nonneg _)) fun r hr => by
          rw [iteratedDeriv_sub (hf _ hμ).contDiffAt (hg _ hμ).contDiffAt, le_div_iff₀
            (by exact_mod_cast he), mul_comm]
          exact hM i r hr
      rwa [mul_div_cancel₀ _ (by exact_mod_cast he.ne')] at hbound
  calc ‖P * reindex σ σ (blockDiagonal' fun i => pfc (f - g) (jordanBlock (e i) (μ i))) * P⁻¹‖
      ≤ ‖P‖ * ‖reindex σ σ (blockDiagonal' fun i => pfc (f - g) (jordanBlock (e i) (μ i)))‖ *
          ‖P⁻¹‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖P‖ * M * ‖P⁻¹‖ := by
        rw [reindex_apply, l2_opNorm_submatrix_equiv]
        gcongr
    _ = ‖P‖ * ‖P⁻¹‖ * M := by ring

end Jordan

section SchurAux

variable {N : ℕ}

/-- If $Q$ is unitary and $f$, $g$ are analytic on a set $\Omega$ that contains the spectrum of $A$,
then $f(A) - g(A) = Q \, (f - g)(Q^H A Q) \, Q^H$. -/
private theorem pfc_sub_eq_unitary_conj {A Q : Matrix (Fin N) (Fin N) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin N) ℂ) {Ω : Set ℂ} (hAΩ : spectrum ℂ A ⊆ Ω) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω) :
    pfc f A - pfc g A = Q * pfc (f - g) (star Q * A * Q) * star Q := by
  have hroot : ∀ z ∈ (minpoly ℂ A).roots, z ∈ Ω := fun z hz =>
    hAΩ (spectrum.mem_of_mem_roots_minpoly hz)
  have hQi : Q⁻¹ = star Q := inv_eq_left_inv (mem_unitaryGroup_iff'.1 hQ)
  have hA : A = Q * (star Q * A * Q) * Q⁻¹ := by
    rw [hQi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hQ,
      Matrix.one_mul, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hQ, Matrix.mul_one]
  -- stating the unit separately avoids a slow unification of the two `Monoid` instance paths
  have hu : IsUnit Q := isUnit_of_mem_unitaryGroup hQ
  have hc := pfc_conj hu (f - g) (star Q * A * Q)
  rw [← hA, hQi] at hc
  rw [← hc]
  exact (pfc_sub (fun z hz => (hf z (hroot z hz)).contDiffAt)
    (fun z hz => (hg z (hroot z hz)).contDiffAt)).symm

end SchurAux

section Schur

open scoped Matrix.Norms.Frobenius

variable {n : Type*} [LinearOrder n]

/-- Let $i < j$ and let $s$ be a set of indices strictly between $i$ and $j$. If $U_{pq} = |T_{pq}|$
for all $p < q$, the modulus of the product of the entries of $T$ along the increasing path from
$i$ through $s$ to $j$ is the product of the entries of $U$ along the same path. -/
private theorem norm_pathProd_path [LocallyFiniteOrder n] {T : Matrix n n ℂ} {U : Matrix n n ℝ}
    (hU : ∀ p q, p < q → U p q = ‖T p q‖) {i j : n} (hij : i < j) {s : Finset n}
    (hs : s ⊆ Finset.Ioo i j) : ‖pathProd T (path i s j)‖ = pathProd U (path i s j) := by
  classical
  induction s using Finset.induction_on_min generalizing i with
  | empty => rw [pathProd_path_empty, pathProd_path_empty, hU i j hij]
  | insert a s ha ih =>
    have ha' := Finset.mem_Ioo.1 (hs (Finset.mem_insert_self a s))
    have hsa : s ⊆ Finset.Ioo a j := fun x hx =>
      Finset.mem_Ioo.2 ⟨ha x hx, (Finset.mem_Ioo.1 (hs (Finset.mem_insert_of_mem hx))).2⟩
    rw [pathProd_path_insert _ hsa, pathProd_path_insert _ hsa, norm_mul, hU i a ha'.1,
      ih ha'.2 hsa]

variable {N : ℕ}

/-- The entrywise modulus $|N|$ of the strictly upper triangular part
$N = T - \operatorname{diag}(T)$ of $T$ has the entry $0$ at $(p, p)$ and $|T_{pq}|$ at $(p, q)$
with $p \neq q$. -/
private theorem absStrictUpper_apply (T : Matrix (Fin N) (Fin N) ℂ) (p q : Fin N) :
    ((T - diagonal T.diag).map fun z => ‖z‖) p q = if p = q then 0 else ‖T p q‖ := by
  rw [map_apply, Matrix.sub_apply]
  split_ifs with h
  · subst h
    rw [diagonal_apply_eq, diag_apply, sub_self, norm_zero]
  · rw [diagonal_apply_ne _ h, sub_zero]

/-- **The entrywise Schur bound.** Let $T \in \mathbb{C}^{n \times n}$ be upper triangular, let
$\Omega \subseteq \mathbb{C}$ be convex and contain the diagonal entries of $T$, let $h$ be
analytic at every point of $\Omega$, and let $|h^{(r)}(z)| \le \delta_r$ for all $r$ and
$z \in \Omega$. Then $|h(T)_{ij}| \le \sum_{r<n} (\delta_r / r!) (|N|^r)_{ij}$ for all $i$ and
$j$, where $|N|$ is the entrywise modulus of $T - \operatorname{diag}(T)$. This is a step of the
proof of Theorem 9.2.2 of [golub2013matrix]. -/
private theorem norm_pfc_apply_le {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.IsUpperTriangular)
    {Ω : Set ℂ} (hΩ : Convex ℝ Ω) (hTΩ : ∀ k, T k k ∈ Ω) {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h Ω)
    {δ : ℕ → ℝ} (hδ : ∀ r, ∀ z ∈ Ω, ‖iteratedDeriv r h z‖ ≤ δ r) (i j : Fin N) :
    ‖pfc h T i j‖ ≤ ∑ r ∈ Finset.range N, δ r / r.factorial *
      (((T - diagonal T.diag).map fun z => ‖z‖) ^ r) i j := by
  classical
  set U : Matrix (Fin N) (Fin N) ℝ := (T - diagonal T.diag).map fun z => ‖z‖ with hUdef
  have hUent : ∀ p q, p < q → U p q = ‖T p q‖ := fun p q hpq => by
    rw [hUdef, absStrictUpper_apply, ite_eq_right hpq.ne]
  have hUstrict : ∀ p q, q ≤ p → U p q = 0 := fun p q hqp => by
    rw [hUdef, absStrictUpper_apply]
    split_ifs with h
    · rfl
    · rw [hT (lt_of_le_of_ne hqp (Ne.symm h)), norm_zero]
  have hUnonneg : ∀ r p q, 0 ≤ (U ^ r) p q := by
    intro r
    induction r with
    | zero => intro p q; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    | succ r ih =>
      intro p q
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_nonneg fun k _ => mul_nonneg (ih p k) ?_
      rw [hUdef, absStrictUpper_apply]
      split_ifs
      · exact le_rfl
      · exact norm_nonneg _
  have hδ0 : ∀ r, 0 ≤ δ r := fun r => (norm_nonneg _).trans (hδ r _ (hTΩ i))
  have hterm : ∀ r, 0 ≤ δ r / r.factorial * (U ^ r) i j := fun r =>
    mul_nonneg (div_nonneg (hδ0 r) (Nat.cast_nonneg _)) (hUnonneg r i j)
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [pfc_apply_eq_sum_divDiff hT h hij]
    calc ‖∑ s ∈ (Finset.Ioo i j).powerset,
          pathProd T (path i s j) * divDiff h ((path i s j).map fun k => T k k)‖
        ≤ ∑ s ∈ (Finset.Ioo i j).powerset,
            pathProd U (path i s j) * (δ (s.card + 1) / (s.card + 1).factorial) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
          have hs' := Finset.mem_powerset.1 hs
          rw [norm_mul, norm_pathProd_path hUent hij hs']
          refine mul_le_mul_of_nonneg_left ?_ ((norm_pathProd_path hUent hij hs') ▸
            norm_nonneg _)
          refine Hermite.norm_divDiff_le hΩ hh ?_ ?_ (hδ _)
          · simp [path]
          · simp only [Multiset.mem_coe, List.mem_map]
            rintro x ⟨k, -, rfl⟩
            exact hTΩ k
      _ = ∑ r ∈ Finset.range ((Finset.Ioo i j).card + 1),
            δ (r + 1) / (r + 1).factorial * (U ^ (r + 1)) i j := by
          rw [Finset.powerset_card_disjiUnion]
          refine (Finset.sum_disjiUnion _ _ _).trans (Finset.sum_congr rfl fun r _ => ?_)
          rw [pow_succ_apply_eq_sum_pathProd hUstrict r hij, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [(Finset.mem_powersetCard.1 hs).2]
          ring
      _ = ∑ r ∈ (Finset.range ((Finset.Ioo i j).card + 1)).map (addRightEmbedding 1),
            δ r / r.factorial * (U ^ r) i j :=
          (Finset.sum_map (Finset.range _) (addRightEmbedding 1)
            fun r => δ r / r.factorial * (U ^ r) i j).symm
      _ ≤ ∑ r ∈ Finset.range N, δ r / r.factorial * (U ^ r) i j := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) fun r _ _ => hterm r
          obtain ⟨r', hr', rfl⟩ := Finset.mem_map.1 hr
          rw [Finset.mem_range] at hr' ⊢
          have hc := Fin.card_Ioo i j
          have : (i : ℕ) < j := hij
          simp only [addRightEmbedding_apply]
          omega
  · subst hij
    rw [pfc_apply_self_of_isUpperTriangular hT]
    have h0 := Finset.single_le_sum (f := fun r => δ r / r.factorial * (U ^ r) i i)
      (fun r _ => hterm r) (Finset.mem_range.2 (Fin.pos i))
    simp only [pow_zero, one_apply_eq, Nat.factorial_zero, Nat.cast_one, div_one,
      mul_one] at h0
    have := hδ 0 _ (hTΩ i)
    rw [iteratedDeriv_zero] at this
    linarith
  · rw [(BlockTriangular.pfc hT h) hij, norm_zero]
    exact Finset.sum_nonneg fun r _ => hterm r

/-- Under the hypotheses of the entrywise Schur bound, $\|h(T)\|_F \le \sum_{r<n} \delta_r \| |N|^r
\|_F / r!$ for an upper triangular $T$. -/
private theorem frobenius_norm_pfc_le {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.IsUpperTriangular)
    {Ω : Set ℂ} (hΩ : Convex ℝ Ω) (hTΩ : ∀ k, T k k ∈ Ω) {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h Ω)
    {δ : ℕ → ℝ} (hδ : ∀ r, ∀ z ∈ Ω, ‖iteratedDeriv r h z‖ ≤ δ r) :
    ‖pfc h T‖ ≤ ∑ r ∈ Finset.range N,
      δ r * ‖((T - diagonal T.diag).map fun z => ‖z‖) ^ r‖ / r.factorial := by
  set U : Matrix (Fin N) (Fin N) ℝ := (T - diagonal T.diag).map fun z => ‖z‖ with hU
  have hE : ∀ i j, ‖pfc h T i j‖
      ≤ (∑ r ∈ Finset.range N, (δ r / r.factorial) • U ^ r) i j := fun i j => by
    refine (norm_pfc_apply_le hT hΩ hTΩ hh hδ i j).trans_eq ?_
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rfl
  refine (frobenius_norm_le_of_forall_norm_le fun i j =>
      (hE i j).trans (Real.le_norm_self _)).trans
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_))
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) (Finset.mem_range.1 hr)
  have hδ0 := (norm_nonneg _).trans (hδ r _ (hTΩ ⟨0, hN⟩))
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg hδ0 (Nat.cast_nonneg _))]
  exact le_of_eq (by ring)

/-- **The Schur bound.** Let $A, Q \in \mathbb{C}^{n \times n}$ with $Q$ unitary, such that
$T = Q^H A Q$ is upper triangular, and write $T = \operatorname{diag}(T) + N$ with $N$ strictly
upper triangular. Let $\Omega \subseteq \mathbb{C}$ be convex and contain the spectrum of $A$,
let $f, g : \mathbb{C} \to \mathbb{C}$ be analytic at every point of $\Omega$, and let
$\delta_r \in \mathbb{R}$ satisfy
$$|(f - g)^{(r)}(z)| \le \delta_r \qquad \text{for all } r \in \mathbb{N} \text{ and } z \in
  \Omega.$$
Then
$$\|f(A) - g(A)\|_F \le \sum_{r=0}^{n-1} \delta_r \frac{\| |N|^r \|_F}{r!},$$
where $|N|$ is the matrix of the moduli of the entries of $N$. This is Theorem 9.2.2 of
[golub2013matrix].

A Schur form exists by `Matrix.exists_unitary_conj_upperTriangular`. The bounds $\delta_r$ are
hypotheses, so $\Omega$ need not be compact; `Matrix.frobenius_norm_pfc_sub_le_of_isCompact` is
the form with the suprema of [golub2013matrix]. The proof uses the unitary invariance of the
norm. Entrywise, Theorem 9.1.4 of [golub2013matrix] (`Matrix.pfc_apply_eq_sum_divDiff`) and the
Hermite–Genocchi bound (9.2.1) (`Hermite.norm_divDiff_le`) give $|h(T)_{ij}| \le \sum_r
(\delta_r / r!) (|N|^r)_{ij}$ through the path expansion (9.2.2)
(`Matrix.pow_succ_apply_eq_sum_pathProd`). The monotonicity of the Frobenius norm and the
triangle inequality complete the proof. -/
theorem frobenius_norm_pfc_sub_le {A Q : Matrix (Fin N) (Fin N) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin N) ℂ) (hT : (star Q * A * Q).IsUpperTriangular) {Ω : Set ℂ}
    (hΩ : Convex ℝ Ω) (hAΩ : spectrum ℂ A ⊆ Ω) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hg : AnalyticOnNhd ℂ g Ω) {δ : ℕ → ℝ}
    (hδ : ∀ r, ∀ z ∈ Ω, ‖iteratedDeriv r (f - g) z‖ ≤ δ r) :
    ‖pfc f A - pfc g A‖ ≤ ∑ r ∈ Finset.range N,
      δ r * ‖((star Q * A * Q - diagonal (star Q * A * Q).diag).map fun z => ‖z‖) ^ r‖
        / r.factorial := by
  have hspec : spectrum ℂ (star Q * A * Q) = spectrum ℂ A := by
    rw [star_eq_conjTranspose, spectrum_conjTranspose_mul_mul hQ]
  have hTΩ : ∀ k, (star Q * A * Q) k k ∈ Ω := fun k => by
    have : (star Q * A * Q) k k ∈ spectrum ℂ (star Q * A * Q) :=
      hT.spectrum_eq ▸ Set.mem_range_self k
    rw [hspec] at this
    exact hAΩ this
  have hpfc := pfc_sub_eq_unitary_conj hQ hAΩ hf hg
  have hsQ : star Q ∈ unitaryGroup (Fin N) ℂ := Unitary.star_mem hQ
  have hu : ‖Q * pfc (f - g) (star Q * A * Q) * star Q‖ = ‖pfc (f - g) (star Q * A * Q)‖ :=
    frobenius_norm_unitary_mul_mul_unitary hQ _ hsQ
  rw [hpfc, hu]
  exact frobenius_norm_pfc_le hT hΩ hTΩ (hf.sub hg) hδ

/-- **The Schur bound with suprema.** Let $A, Q \in \mathbb{C}^{n \times n}$ with $Q$ unitary, such
that $T = Q^H A Q$ is upper triangular, and write $T = \operatorname{diag}(T) + N$ with $N$
strictly upper triangular. Let $\Omega \subseteq \mathbb{C}$ be compact and convex and contain
the spectrum of $A$, and let $f, g : \mathbb{C} \to \mathbb{C}$ be analytic at every point of
$\Omega$. Then
$$\|f(A) - g(A)\|_F \le \sum_{r=0}^{n-1} \delta_r \frac{\| |N|^r \|_F}{r!}, \qquad \delta_r =
  \sup_{z \in \Omega} |f^{(r)}(z) - g^{(r)}(z)|.$$
This is Theorem 9.2.2 of [golub2013matrix] with the suprema of the source.

[golub2013matrix] asks only that $\Omega$ is closed and convex. For an unbounded $\Omega$ the
supremum can be infinite, and the supremum `sSup` of an unbounded set of reals is $0$ in Lean,
so the statement here asks that $\Omega$ is compact. The derivatives are continuous on $\Omega$,
so the suprema bound them and `Matrix.frobenius_norm_pfc_sub_le` applies. -/
theorem frobenius_norm_pfc_sub_le_of_isCompact {A Q : Matrix (Fin N) (Fin N) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin N) ℂ) (hT : (star Q * A * Q).IsUpperTriangular) {Ω : Set ℂ}
    (hΩc : IsCompact Ω) (hΩ : Convex ℝ Ω) (hAΩ : spectrum ℂ A ⊆ Ω) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω) :
    ‖pfc f A - pfc g A‖ ≤ ∑ r ∈ Finset.range N,
      sSup ((fun z => ‖iteratedDeriv r (f - g) z‖) '' Ω) *
        ‖((star Q * A * Q - diagonal (star Q * A * Q).diag).map fun z => ‖z‖) ^ r‖
          / r.factorial := by
  refine frobenius_norm_pfc_sub_le hQ hT hΩ hAΩ hf hg fun r z hz => ?_
  have hcont : ContinuousOn (fun z => ‖iteratedDeriv r (f - g) z‖) Ω := by
    rw [iteratedDeriv_eq_iterate]
    exact ((hf.sub hg).iterated_deriv r).continuousOn.norm
  exact le_csSup (hΩc.bddAbove_image hcont) (Set.mem_image_of_mem _ hz)

end Schur

section Simpson

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [FiniteDimensional ℂ 𝔸]

/-- **The composite Simpson rule for $\int_a^b f(tA) \, dt$.** Let $A$ be an element of a
finite-dimensional normed $\mathbb{C}$-algebra, for example a complex matrix with the spectral
norm. Let $a < b$, let $N \ge 1$ and $H = (b - a)/N$, and let $f : \mathbb{C} \to \mathbb{C}$ be
analytic at $t\mu$ for every $t \in [a, b]$ and every eigenvalue $\mu$ of $A$. Let
$$S = \sum_{j=0}^{N-1} \frac{H}{6} \Bigl(f(t_j A) + 4 f\bigl((t_j + \tfrac{H}{2}) A\bigr) +
  f(t_{j+1} A)\Bigr), \qquad t_j = a + jH,$$
be the composite Simpson sum on $N$ panels of width $H$. Then, with $h = H/2$,
$$\Bigl\|\int_a^b f(tA) \, dt - S\Bigr\| \le \frac{h^4 (b - a)}{180} \sup_{t \in [a, b]} \|A^4
  f^{(4)}(tA)\|.$$
This is (9.2.7) of [golub2013matrix], §9.2.6, where the interval is divided into $m = 2N$
subintervals of width $h$ with the weights $1, 4, 2, \dots, 4, 1$.

The printed (9.2.7) does not have the factor $A^4$. It is needed, because
$\frac{d^4}{dt^4} f(tA) = A^4 f^{(4)}(tA)$ (`hasDerivAt_pfc_smul`, iterated). The bound is
`Quadrature.norm_sub_simpsonSum_le` with $H^4 / 2880 = h^4 / 180$. -/
theorem norm_integral_pfc_smul_sub_simpsonSum_le (A : 𝔸) {f : ℂ → ℂ} {a b H : ℝ} (hab : a < b)
    {N : ℕ} (hN : 0 < N) (hH : H = (b - a) / N)
    (hf : ∀ t ∈ Set.Icc a b, ∀ μ ∈ spectrum ℂ A, AnalyticAt ℂ f (t * μ)) :
    ‖(∫ t in a..b, pfc f ((t : ℂ) • A)) - ∑ j ∈ Finset.range N, (H / 6) •
        (pfc f (((a + j * H : ℝ) : ℂ) • A) + (4 : ℝ) • pfc f (((a + j * H + H / 2 : ℝ) : ℂ) • A)
          + pfc f (((a + (j + 1) * H : ℝ) : ℂ) • A))‖
      ≤ (H / 2) ^ 4 * (b - a) / 180 *
        sSup ((fun t : ℝ => ‖A ^ 4 * pfc (iteratedDeriv 4 f) ((t : ℂ) • A)‖) '' Set.Icc a b) := by
  have ha : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hs : (minpoly ℂ A).Splits := IsAlgClosed.splits _
  set G : ℕ → ℝ → 𝔸 := fun k t => A ^ k * pfc (deriv^[k] f) ((t : ℂ) • A) with hGdef
  have hG : ∀ k, ∀ t ∈ Set.Icc a b, HasDerivAt (G k) (G (k + 1) t) t := by
    intro k t ht
    have h1 := hasDerivAt_pfc_smul ha hs (f := deriv^[k] f) (t := (t : ℂ))
      fun μ hμ => (hf t ht μ hμ).iterated_deriv k
    have h2 := (h1.scomp t Complex.ofRealCLM.hasDerivAt).const_mul (A ^ k)
    convert h2 using 1
    · rfl
    · simp only [hGdef, Function.iterate_succ_apply', pow_succ, mul_assoc,
        Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]
  have hcont : ContinuousOn (G 4) (Set.Icc a b) := fun t ht =>
    (hG 4 t ht).continuousAt.continuousWithinAt
  have hG4 : G 4 = fun t : ℝ => A ^ 4 * pfc (iteratedDeriv 4 f) ((t : ℂ) • A) := by
    funext t
    simp only [hGdef, iteratedDeriv_eq_iterate]
  have hbdd : BddAbove ((fun t : ℝ => ‖A ^ 4 * pfc (iteratedDeriv 4 f) ((t : ℂ) • A)‖) ''
      Set.Icc a b) := by
    have : (fun t : ℝ => ‖A ^ 4 * pfc (iteratedDeriv 4 f) ((t : ℂ) • A)‖)
        = fun t => ‖G 4 t‖ := by rw [hG4]
    rw [this]
    exact isCompact_Icc.bddAbove_image hcont.norm
  have hS := Quadrature.norm_sub_simpsonSum_le hab hN hH (hG 0) (hG 1) (hG 2) (hG 3) hcont
    (M := sSup ((fun t : ℝ => ‖A ^ 4 * pfc (iteratedDeriv 4 f) ((t : ℂ) • A)‖) '' Set.Icc a b))
    fun t ht => by rw [hG4]; exact le_csSup hbdd (Set.mem_image_of_mem _ ht)
  have hG0 : G 0 = fun t : ℝ => pfc f ((t : ℂ) • A) := by
    funext t
    simp [hGdef]
  rw [hG0] at hS
  refine hS.trans (le_of_eq ?_)
  ring

end Simpson

end Matrix
