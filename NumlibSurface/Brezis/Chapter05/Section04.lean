/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Numlib.Analysis.InnerProductSpace.HilbertSum
import Numlib.Analysis.InnerProductSpace.OrthonormalSeries

/-!
# Brezis, Section 5.4: Hilbert sums, orthonormal bases

This module formalizes Section 5.4 of [brezis2011functional] for a real Hilbert space $H$ with
scalar product $(u, v)$ and norm $|u|$. A sequence $(E_n)$ of closed subspaces makes $H$ the Hilbert
sum $H = \bigoplus_n E_n$ if the $E_n$ are mutually orthogonal and the linear space that they span
is dense in $H$. Then every $u \in H$ is the sum of its orthogonal projections,
$u = \sum_n P_{E_n} u$, and $|u|^2 = \sum_n |P_{E_n} u|^2$ (Theorem 5.9). An orthonormal basis is a
sequence $(e_n)$ of orthonormal vectors whose span is dense. It gives the expansion
$u = \sum_k (u, e_k) e_k$ and the Parseval identity (Corollary 5.10), and every separable Hilbert
space has one (Theorem 5.11).

The proofs specialize the backbone modules `Numlib.Analysis.InnerProductSpace.HilbertSum` and
`Numlib.Analysis.InnerProductSpace.OrthonormalSeries`, and Mathlib's `HilbertBasis`,
`exists_hilbertBasis` and `OrthogonalFamily`.

## Main definitions

* Section 5.4, definition of a Hilbert sum, `Brezis.Chapter05.IsHilbertSumOf`:
  $H = \bigoplus_n E_n$, identified with Mathlib's `IsHilbertSum` by
  `Brezis.Chapter05.isHilbertSumOf_iff`.
* Section 5.4, definition of an orthonormal basis, `Brezis.Chapter05.IsOrthonormalBasis`: an
  orthonormal sequence with dense span, identified with `HilbertBasis ℕ ℝ H` by
  `Brezis.Chapter05.isOrthonormalBasis_iff`.

## Main results

* Theorem 5.9, `Brezis.Chapter05.theorem_5_9`: if $H = \bigoplus_n E_n$, then $u = \sum_n P_{E_n} u$
  and $|u|^2 = \sum_n |P_{E_n} u|^2$.
* Lemma 5.1, `Brezis.Chapter05.lemma_5_1`: a series of mutually orthogonal vectors with
  $\sum_k |v_k|^2 < \infty$ converges, and its sum $S$ has $|S|^2 = \sum_k |v_k|^2$.
* Theorem 5.9, `Brezis.Chapter05.theorem_5_9_closure`: without the density condition,
  $\sum_n P_{E_n} u$ converges to the projection of $u$ onto the closed span, and Bessel's
  inequality holds.
* Corollary 5.10, `Brezis.Chapter05.corollary_5_10`: for an orthonormal basis,
  $u = \sum_k (u, e_k) e_k$ and $|u|^2 = \sum_k (u, e_k)^2$.
* Corollary 5.10, `Brezis.Chapter05.corollary_5_10_converse`: every square-summable sequence
  $(\alpha_k)$ is the coefficient sequence of some $u \in H$.
* Remark 9, `Brezis.Chapter05.remark_5_9`: the series $\sum_k (u, e_k) e_k$ need not converge
  absolutely.
* Theorem 5.11, `Brezis.Chapter05.theorem_5_11`: a separable Hilbert space has a countable Hilbert
  basis.
* Theorem 5.11, `Brezis.Chapter05.theorem_5_11_nat`: a separable infinite-dimensional Hilbert space
  has an orthonormal basis that is a sequence.
* Remark 10, `Brezis.Chapter05.remark_5_10`: a separable infinite-dimensional Hilbert space is
  isometrically isomorphic to $\ell^2$.
* Remark 11, `Brezis.Chapter05.remark_5_11`: every Hilbert space has a Hilbert basis.

## Conventions

* Sequences are indexed by `ℕ` and start at $0$; the source starts at $1$. The partial sum
  $S_n = \sum_{k=1}^n$ of the source is the sum over `Finset.range n`, that is, over $k < n$.
* A series $\sum_{k=1}^\infty$ of the source is a limit of partial sums. The results state this
  sequential form, `Tendsto (fun n => ∑ k ∈ Finset.range n, …) atTop (𝓝 …)`, where the source
  displays a series of vectors, and Mathlib's unconditional `HasSum` for the Parseval identities.
  For orthogonal series the two notions agree.

## Implementation notes

* The closed subspaces $E_n$ are `E : ℕ → ClosedSubmodule ℝ H`. The coercion to `Submodule ℝ H` has
  an orthogonal projection in a complete space, so $P_{E_n} u$ is
  `(E n : Submodule ℝ H).starProjection u`.
* The closedness of the $E_n$ is a hypothesis of the theorems, not a part of the predicate
  `Brezis.Chapter05.IsHilbertSumOf`.

## Deviations from the source

* **Theorem 5.11** (reading). The source asserts an orthonormal basis $(e_n)_{n \ge 1}$, which
  cannot exist in finite dimension. The library states a countable Hilbert basis in every dimension,
  and the sequence form for infinite-dimensional $H$. See `Brezis.Chapter05.theorem_5_11` and
  `Brezis.Chapter05.theorem_5_11_nat`.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ### Hilbert sums -/

omit [CompleteSpace H] in
/-- **Section 5.4** of [brezis2011functional], definition of a Hilbert sum. Let $(E_n)$ be a
sequence of subspaces of an inner product space $H$. Then $H$ is the **Hilbert sum** of the
$E_n$, written $H = \bigoplus_n E_n$, if (a) the $E_n$ are mutually orthogonal, that is,
$(u, v) = 0$ for all $u \in E_m$ and $v \in E_n$ with $m \neq n$, and (b) the linear space
spanned by $\bigcup_n E_n$ is dense in $H$.

The source assumes that the $E_n$ are closed. Here closedness is a hypothesis of the theorems,
not a part of the predicate. The span in (b) is the supremum `⨆ n, E n` of the submodules, as in
footnote 3 of the source. -/
def IsHilbertSumOf (E : ℕ → Submodule ℝ H) : Prop :=
  (∀ m n, m ≠ n → ∀ u ∈ E m, ∀ v ∈ E n, ⟪u, v⟫_ℝ = 0) ∧
    Dense ((⨆ n, E n : Submodule ℝ H) : Set H)

omit [CompleteSpace H] in
/-- If $H = \bigoplus_n E_n$ in the sense of `Brezis.Chapter05.IsHilbertSumOf`, then the subspaces
$E_n$, with their inclusions into $H$, form an orthogonal family in the sense of Mathlib's
`OrthogonalFamily`. This is clause (a) of the definition. -/
theorem IsHilbertSumOf.orthogonalFamily {E : ℕ → Submodule ℝ H} (h : IsHilbertSumOf E) :
    OrthogonalFamily ℝ (fun n => E n) fun n => (E n).subtypeₗᵢ :=
  orthogonalFamily_iff_pairwise.2 fun m n hmn =>
    Submodule.isOrtho_iff_inner_eq.2 fun u hu v hv => h.1 m n hmn u hu v hv

/-- Let $(E_n)$ be a sequence of closed subspaces of a Hilbert space $H$. Then $H = \bigoplus_n E_n$
in the sense of the source (`Brezis.Chapter05.IsHilbertSumOf`) if and only if $H$ is the Hilbert
sum of the $E_n$ in the sense of Mathlib's `IsHilbertSum`: the $E_n$ form an orthogonal family
and the induced isometry from $\ell^2$ of the $E_n$ to $H$ is onto. -/
theorem isHilbertSumOf_iff (E : ℕ → ClosedSubmodule ℝ H) :
    IsHilbertSumOf (fun n => (E n : Submodule ℝ H)) ↔
      IsHilbertSum ℝ (fun n => (E n : Submodule ℝ H)) fun n => (E n : Submodule ℝ H).subtypeₗᵢ := by
  have : ∀ n, CompleteSpace (E n : Submodule ℝ H) := fun n => (E n).isClosed.completeSpace_coe
  constructor
  · intro h
    refine IsHilbertSum.mkInternal (fun n => (E n : Submodule ℝ H)) h.orthogonalFamily ?_
    rw [Submodule.dense_iff_topologicalClosure_eq_top.1 h.2]
  · intro h
    refine ⟨fun m n hmn u hu v hv => ?_, ?_⟩
    · exact (orthogonalFamily_iff_pairwise.1 h.OrthogonalFamily hmn).inner_eq hu hv
    · rw [Submodule.dense_iff_topologicalClosure_eq_top]
      have hrange := h.OrthogonalFamily.range_linearIsometry
      rw [LinearMap.range_eq_top.2 h.surjective_isometry] at hrange
      simpa only [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype] using hrange.symm

/-- **Lemma 5.1** of [brezis2011functional]. Let $H$ be a Hilbert space and let $(v_n)$ be a
sequence in $H$ with $(v_m, v_n) = 0$ for $m \neq n$ and $\sum_k |v_k|^2 < \infty$. Then the
partial sums $S_n = \sum_{k<n} v_k$ converge to some $S \in H$, and
$$|S|^2 = \sum_{k=0}^\infty |v_k|^2.$$

This is display (23) of the source. -/
theorem lemma_5_1 {v : ℕ → H} (hv : Pairwise fun m n => ⟪v m, v n⟫_ℝ = 0)
    (hsum : Summable fun k => ‖v k‖ ^ 2) :
    ∃ S, Tendsto (fun n => ∑ k ∈ Finset.range n, v k) atTop (𝓝 S) ∧
      ‖S‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 := by
  have hS := ((summable_iff_summable_norm_sq_of_pairwise_inner_eq_zero hv).2 hsum).hasSum
  exact ⟨_, hS.tendsto_sum_nat, (hasSum_norm_sq_of_pairwise_inner_eq_zero hv hS).tsum_eq.symm⟩

/-- **Theorem 5.9** of [brezis2011functional]. Let $(E_n)$ be a sequence of closed subspaces of a
Hilbert space $H$ with $H = \bigoplus_n E_n$. For $u \in H$ put $u_n = P_{E_n} u$ and
$S_n = \sum_{k<n} u_k$. Then $S_n \to u$ as $n \to \infty$ (display (19)), and
$$\sum_{k=0}^\infty |u_k|^2 = |u|^2$$
(the Bessel–Parseval identity, display (20)).

The projection $P_{E_n} u$ is `(E n : Submodule ℝ H).starProjection u`, and the identity is
stated with `HasSum`. -/
theorem theorem_5_9 (E : ℕ → ClosedSubmodule ℝ H)
    (hE : IsHilbertSumOf fun n => (E n : Submodule ℝ H)) (u : H) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (E k : Submodule ℝ H).starProjection u) atTop
        (𝓝 u) ∧
      HasSum (fun k => ‖(E k : Submodule ℝ H).starProjection u‖ ^ 2) (‖u‖ ^ 2) := by
  have hdense : (⨆ n, (E n : Submodule ℝ H)).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.1 hE.2
  exact ⟨(hE.orthogonalFamily.hasSum_starProjection_of_dense hdense u).tendsto_sum_nat,
    hE.orthogonalFamily.hasSum_norm_sq_starProjection_of_dense hdense u⟩

/-- **Theorem 5.9** of [brezis2011functional], the case without the density condition. Let $(E_n)$
be a sequence of mutually orthogonal closed subspaces of a Hilbert space $H$, and let $\bar F$
be the closure of the linear space spanned by $\bigcup_n E_n$. Then for every $u \in H$ the
partial sums $S_n = \sum_{k<n} P_{E_k} u$ converge to $P_{\bar F} u$, and
$$\sum_{k=0}^\infty |P_{E_k} u|^2 \le |u|^2$$
(Bessel's inequality).

The proof of Theorem 5.9 in the source establishes this statement "even without assumption (b)",
display (26). -/
theorem theorem_5_9_closure (E : ℕ → ClosedSubmodule ℝ H)
    (hE : ∀ m n, m ≠ n → ∀ u ∈ E m, ∀ v ∈ E n, ⟪u, v⟫_ℝ = 0) (u : H) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (E k : Submodule ℝ H).starProjection u) atTop
        (𝓝 ((⨆ n, (E n : Submodule ℝ H)).topologicalClosure.starProjection u)) ∧
      ∑' k, ‖(E k : Submodule ℝ H).starProjection u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hV : OrthogonalFamily ℝ (fun n => (E n : Submodule ℝ H))
      fun n => (E n : Submodule ℝ H).subtypeₗᵢ :=
    orthogonalFamily_iff_pairwise.2 fun m n hmn =>
      Submodule.isOrtho_iff_inner_eq.2 fun u hu v hv => hE m n hmn u hu v hv
  exact ⟨(hV.hasSum_starProjection u).tendsto_sum_nat, hV.tsum_norm_sq_starProjection_le u⟩

/-! ### Orthonormal bases -/

omit [CompleteSpace H] in
/-- **Section 5.4** of [brezis2011functional], definition of an orthonormal basis. A sequence
$(e_n)$ in an inner product space $H$ is an **orthonormal basis** (or Hilbert basis) of $H$ if
(i) $|e_n| = 1$ for all $n$ and $(e_m, e_n) = 0$ for all $m \neq n$, and (ii) the linear space
spanned by the $e_n$ is dense in $H$.

Condition (i) is Mathlib's `Orthonormal`. The bundled object is `HilbertBasis ℕ ℝ H`, see
`Brezis.Chapter05.isOrthonormalBasis_iff`. Mathlib's `OrthonormalBasis` is the structure for
finite dimension and is not used. -/
def IsOrthonormalBasis (e : ℕ → H) : Prop :=
  Orthonormal ℝ e ∧ Dense ((Submodule.span ℝ (Set.range e) : Submodule ℝ H) : Set H)

/-- A sequence $(e_n)$ in a Hilbert space $H$ is an orthonormal basis in the sense of
`Brezis.Chapter05.IsOrthonormalBasis` if and only if it is the sequence of vectors of a Hilbert
basis `HilbertBasis ℕ ℝ H`. -/
theorem isOrthonormalBasis_iff (e : ℕ → H) :
    IsOrthonormalBasis e ↔ ∃ b : HilbertBasis ℕ ℝ H, ⇑b = e := by
  constructor
  · rintro ⟨hon, hdense⟩
    exact ⟨HilbertBasis.mk hon (Submodule.dense_iff_topologicalClosure_eq_top.1 hdense).ge,
      HilbertBasis.coe_mk hon _⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b.orthonormal, Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span⟩

/-- **Corollary 5.10** of [brezis2011functional]. Let $(e_n)$ be an orthonormal basis of a Hilbert
space $H$. Then for every $u \in H$,
$$u = \sum_{k=0}^\infty (u, e_k) e_k, \quad \text{that is,} \quad u = \lim_{n \to \infty}
  \sum_{k<n} (u, e_k) e_k,$$
and $|u|^2 = \sum_{k=0}^\infty (u, e_k)^2$ (Parseval).

The Parseval identity is stated with `HasSum`. -/
theorem corollary_5_10 {e : ℕ → H} (he : IsOrthonormalBasis e) (u : H) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, ⟪u, e k⟫_ℝ • e k) atTop (𝓝 u) ∧
      HasSum (fun k => ⟪u, e k⟫_ℝ ^ 2) (‖u‖ ^ 2) := by
  obtain ⟨b, rfl⟩ := (isOrthonormalBasis_iff e).1 he
  have hsum : HasSum (fun k => ⟪u, b k⟫_ℝ • b k) u := by
    have := b.hasSum_repr u
    simpa only [b.repr_apply_apply, real_inner_comm] using this
  refine ⟨hsum.tendsto_sum_nat, ?_⟩
  have := b.orthonormal.hasSum_mul_of_hasSum hsum hsum
  simpa only [real_inner_self_eq_norm_sq, sq] using this

/-- **Corollary 5.10** of [brezis2011functional], converse. Let $(e_n)$ be an orthonormal basis of a
Hilbert space $H$ and let $(\alpha_n)$ be a real sequence with $\sum_k \alpha_k^2 < \infty$.
Then the partial sums $\sum_{k<n} \alpha_k e_k$ converge to some $u \in H$ with
$(u, e_k) = \alpha_k$ for all $k$ and $|u|^2 = \sum_{k=0}^\infty \alpha_k^2$.

The proof uses only that $(e_n)$ is orthonormal, not the density of its span. -/
theorem corollary_5_10_converse {e : ℕ → H} (he : IsOrthonormalBasis e) {α : ℕ → ℝ}
    (hα : Summable fun k => α k ^ 2) :
    ∃ u, Tendsto (fun n => ∑ k ∈ Finset.range n, α k • e k) atTop (𝓝 u) ∧
      (∀ k, ⟪u, e k⟫_ℝ = α k) ∧ ‖u‖ ^ 2 = ∑' k, α k ^ 2 := by
  have hsum := ((he.1.summable_smul_iff α).2 hα).hasSum
  refine ⟨_, hsum.tendsto_sum_nat, fun k => ?_, ?_⟩
  · rw [real_inner_comm]
    exact he.1.inner_eq_of_hasSum hsum k
  · have := he.1.hasSum_mul_of_hasSum hsum hsum
    rw [real_inner_self_eq_norm_sq] at this
    simpa only [sq] using this.tsum_eq.symm

/-- **Remark 9** in Chapter 5 of [brezis2011functional]. The series of Corollary 5.10 need not
converge absolutely: for every orthonormal basis $(e_n)$ of a Hilbert space $H$ there is
$u \in H$ such that the series $\sum_k |(u, e_k)|$ does not converge.

The vector $u$ has the coefficients $\alpha_k = 1/(k+1)$, which are square-summable but not
summable. The remark in the source is also about the series $\sum_n u_n$ of Theorem 5.9; that
form is this statement for $E_k = \mathbb{R} e_k$. -/
theorem remark_5_9 {e : ℕ → H} (he : IsOrthonormalBasis e) :
    ∃ u, ¬ Summable fun k => |⟪u, e k⟫_ℝ| := by
  have hsq : Summable fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2 := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa only [Nat.cast_add, Nat.cast_one, one_div, inv_pow] using this
  obtain ⟨u, -, hu, -⟩ := corollary_5_10_converse he hsq
  refine ⟨u, fun hs => Real.not_summable_one_div_natCast ?_⟩
  rw [← summable_nat_add_iff 1]
  refine hs.congr fun k => ?_
  rw [hu k, abs_of_nonneg (by positivity)]
  push_cast
  ring

/-- **Theorem 5.11** of [brezis2011functional]. Every separable Hilbert space $H$ has an orthonormal
basis. In the form stated here, which holds in every dimension, there is a countable set
$w \subseteq H$ and a Hilbert basis of $H$ indexed by $w$ whose vectors are the elements of $w$.

**Reading.** The source defines an orthonormal basis as a sequence $(e_n)_{n \ge 1}$, and such a
sequence cannot exist when $H$ is finite dimensional. This declaration states the theorem with a
countable index set, which covers every dimension. The sequence form, for infinite-dimensional
$H$, is `Brezis.Chapter05.theorem_5_11_nat`.

The source proves the theorem by the Gram–Schmidt process on a dense sequence. The proof here
uses Mathlib's `exists_hilbertBasis` and the countability of orthonormal families in a separable
space, through `exists_hilbertBasis_countable`. -/
theorem theorem_5_11 [TopologicalSpace.SeparableSpace H] :
    ∃ (w : Set H) (b : HilbertBasis w ℝ H), w.Countable ∧ ⇑b = ((↑) : w → H) :=
  exists_hilbertBasis_countable ℝ H

/-- **Theorem 5.11** of [brezis2011functional], the form for sequences. Let $H$ be a separable
Hilbert space of infinite dimension. Then there is a sequence $(e_n)$ that is an orthonormal
basis of $H$.

**Reading.** The hypothesis that $H$ is infinite dimensional is added. A finite-dimensional
space contains no infinite orthonormal sequence, so it has no orthonormal basis in the sense of
the source's definition. See `Brezis.Chapter05.theorem_5_11` for the form that holds in every
dimension. -/
theorem theorem_5_11_nat [TopologicalSpace.SeparableSpace H] (h : ¬ FiniteDimensional ℝ H) :
    ∃ e : ℕ → H, IsOrthonormalBasis e := by
  obtain ⟨b⟩ := exists_hilbertBasis_nat ℝ H h
  exact ⟨b, (isOrthonormalBasis_iff b).2 ⟨b, rfl⟩⟩

/-- **Remark 10** in Chapter 5 of [brezis2011functional]. All separable infinite-dimensional Hilbert
spaces are isomorphic and isometric to $\ell^2$: for such a space $H$ there is a linear
isometric isomorphism from $H$ onto $\ell^2$.

The space $\ell^2$ is `lp (fun _ : ℕ => ℝ) 2`. The isometry of the proof is the coordinate map
$u \mapsto ((u, e_n))_n$ of an orthonormal basis $(e_n)$. -/
theorem remark_5_10 [TopologicalSpace.SeparableSpace H] (h : ¬ FiniteDimensional ℝ H) :
    Nonempty (H ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) 2) := by
  obtain ⟨b⟩ := exists_hilbertBasis_nat ℝ H h
  exact ⟨b.repr⟩

/-- **Remark 11** in Chapter 5 of [brezis2011functional]. Every Hilbert space $H$, separable or not,
has an orthonormal basis $(e_i)_{i \in I}$, possibly uncountable: there is a set $w \subseteq H$
and a Hilbert basis of $H$ indexed by $w$ whose vectors are the elements of $w$.

The proof is Zorn's lemma, in the form of Mathlib's `exists_hilbertBasis`. -/
theorem remark_5_11 : ∃ (w : Set H) (b : HilbertBasis w ℝ H), ⇑b = ((↑) : w → H) :=
  exists_hilbertBasis ℝ H

end Brezis.Chapter05

end
