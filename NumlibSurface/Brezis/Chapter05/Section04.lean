import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Numlib.Analysis.InnerProductSpace.HilbertSum
import Numlib.Analysis.InnerProductSpace.OrthonormalSeries

/-!
# Brezis §5.4: Hilbert sums, orthonormal bases

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §5.4, over a real Hilbert space `H`. The two Definition
paragraphs are predicates on `ℕ`-indexed families, as the book has them, each with an `iff` to the
Mathlib object it is (`IsHilbertSum`, `HilbertBasis ℕ ℝ H`); Theorem 5.9 and Lemma 5.1 delegate to
the backbone `Numlib/Analysis/InnerProductSpace/HilbertSum`, Corollary 5.10 to Mathlib's
`HilbertBasis` API and the backbone `Numlib/Analysis/InnerProductSpace/OrthonormalSeries`,
Theorem 5.11 and Remarks 10–11 to `exists_hilbertBasis_countable`, `exists_hilbertBasis_nat` and
Mathlib's `exists_hilbertBasis`.

Two conventions. The book's series `∑_{k=1}^∞` are limits of partial sums; Mathlib's `HasSum`
is unconditional, which for orthogonal series is the same thing, and the nodes state the book's
sequential form (`Tendsto (fun n => ∑ k ∈ Finset.range n, …) atTop (𝓝 …)`, from
`HasSum.tendsto_sum_nat`) where the book displays it and `HasSum` for the Parseval identities.
The book's closed subspaces `Eₙ` are `E : ℕ → ClosedSubmodule ℝ H`; the coercion to
`Submodule ℝ H` carries `HasOrthogonalProjection` in a complete space, so `P_{Eₙ} u` is
`(E n : Submodule ℝ H).starProjection u`.

## Main results

* `IsHilbertSumOf`, `isHilbertSumOf_iff` — `H = ⊕ₙ Eₙ`, and its identification with Mathlib's
  `IsHilbertSum`.
* `lemma_5_1` — a pairwise orthogonal sequence with `∑ |vₖ|² < ∞` is summable, with
  `|S|² = ∑ |vₖ|²`.
* `theorem_5_9`, `theorem_5_9_closure` — the expansion `u = ∑ P_{Eₙ} u` with Bessel–Parseval, and
  the clause "even without (b)": the partial sums converge to `P_{F̄} u`, with Bessel's inequality.
* `IsOrthonormalBasis`, `isOrthonormalBasis_iff` — orthonormal bases, and their identification
  with `HilbertBasis ℕ ℝ H`.
* `corollary_5_10`, `corollary_5_10_converse`, `remark_5_9` — the expansion `u = ∑ (u, eₖ) eₖ`,
  Parseval, the converse for `ℓ²` coefficients, and the failure of absolute convergence.
* `theorem_5_11`, `theorem_5_11_nat`, `remark_5_10`, `remark_5_11` — every separable Hilbert
  space has an orthonormal basis (countable; a sequence in infinite dimension), is isometric to
  `ℓ²`, and every Hilbert space has an orthonormal basis (Zorn).
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ### Hilbert sums -/

omit [CompleteSpace H] in
/-- **Definition.** `H` is the Hilbert sum of the subspaces `Eₙ`, `H = ⊕ₙ Eₙ`: (a) the `Eₙ` are
mutually orthogonal, `(u, v) = 0` for `u ∈ Eₙ`, `v ∈ Eₘ`, `m ≠ n`; (b) the linear space spanned by
`⋃ₙ Eₙ` — the supremum `⨆ n, E n`, footnote 3 — is dense in `H`. Closedness of the `Eₙ` is the
standing assumption of the paragraph and a hypothesis of the theorems, not part of the
predicate. -/
def IsHilbertSumOf (E : ℕ → Submodule ℝ H) : Prop :=
  (∀ m n, m ≠ n → ∀ u ∈ E m, ∀ v ∈ E n, ⟪u, v⟫_ℝ = 0) ∧
    Dense ((⨆ n, E n : Submodule ℝ H) : Set H)

omit [CompleteSpace H] in
/-- Clause (a) of the Definition is the orthogonality of the family of subspaces. -/
theorem IsHilbertSumOf.orthogonalFamily {E : ℕ → Submodule ℝ H} (h : IsHilbertSumOf E) :
    OrthogonalFamily ℝ (fun n => E n) fun n => (E n).subtypeₗᵢ :=
  orthogonalFamily_iff_pairwise.2 fun m n hmn =>
    Submodule.isOrtho_iff_inner_eq.2 fun u hu v hv => h.1 m n hmn u hu v hv

/-- For closed subspaces, the book's predicate is Mathlib's `IsHilbertSum`: the orthogonal family
of the `Eₙ` makes `H` the Hilbert sum of the `Eₙ` (the isometry `ℓ²(Eₙ) → H` is onto). -/
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

/-- **Lemma 5.1.** For a sequence `(vₙ)` in `H` with `(vₘ, vₙ) = 0` for `m ≠ n` and
`∑ |vₖ|² < ∞`, the partial sums `Sₙ = ∑_{k<n} vₖ` converge to some `S`, and
`|S|² = ∑_{k=1}^∞ |vₖ|²` (display (23)). -/
theorem lemma_5_1 {v : ℕ → H} (hv : Pairwise fun m n => ⟪v m, v n⟫_ℝ = 0)
    (hsum : Summable fun k => ‖v k‖ ^ 2) :
    ∃ S, Tendsto (fun n => ∑ k ∈ Finset.range n, v k) atTop (𝓝 S) ∧
      ‖S‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 := by
  have hS := ((summable_iff_summable_norm_sq_of_pairwise_inner_eq_zero hv).2 hsum).hasSum
  exact ⟨_, hS.tendsto_sum_nat, (hasSum_norm_sq_of_pairwise_inner_eq_zero hv hS).tsum_eq.symm⟩

/-- **Theorem 5.9.** If `H` is the Hilbert sum of the closed subspaces `Eₙ`, then for every
`u ∈ H`, with `uₙ = P_{Eₙ} u` and `Sₙ = ∑_{k<n} uₖ`: `Sₙ → u` (display (19)) and
`∑_{k=1}^∞ |uₖ|² = |u|²` (Bessel–Parseval's identity, display (20)). -/
theorem theorem_5_9 (E : ℕ → ClosedSubmodule ℝ H)
    (hE : IsHilbertSumOf fun n => (E n : Submodule ℝ H)) (u : H) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (E k : Submodule ℝ H).starProjection u) atTop
        (𝓝 u) ∧
      HasSum (fun k => ‖(E k : Submodule ℝ H).starProjection u‖ ^ 2) (‖u‖ ^ 2) := by
  have hdense : (⨆ n, (E n : Submodule ℝ H)).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.1 hE.2
  exact ⟨(hE.orthogonalFamily.hasSum_starProjection_of_dense hdense u).tendsto_sum_nat,
    hE.orthogonalFamily.hasSum_norm_sq_starProjection_of_dense hdense u⟩

/-- **Theorem 5.9, the clause its proof establishes "even without assumption (b)"** (display
(26)): for mutually orthogonal closed subspaces `Eₙ` and `F̄` the closure of the space they span,
the partial sums `Sₙ = ∑_{k<n} P_{Eₖ} u` converge to `P_{F̄} u`, and `∑ |uₖ|² ≤ |u|²` (Bessel's
inequality). -/
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
/-- **Definition.** A sequence `(eₙ)` in `H` is an orthonormal basis (Hilbert basis) of `H` if
(i) `|eₙ| = 1` for all `n` and `(eₘ, eₙ) = 0` for `m ≠ n` (Mathlib's `Orthonormal`), and (ii) the
linear space spanned by the `eₙ` is dense in `H`. The bundled object is `HilbertBasis ℕ ℝ H`,
see `isOrthonormalBasis_iff`; Mathlib's `OrthonormalBasis` is the finite structure. -/
def IsOrthonormalBasis (e : ℕ → H) : Prop :=
  Orthonormal ℝ e ∧ Dense ((Submodule.span ℝ (Set.range e) : Submodule ℝ H) : Set H)

/-- The book's orthonormal bases are exactly the `ℕ`-indexed Hilbert bases of Mathlib. -/
theorem isOrthonormalBasis_iff (e : ℕ → H) :
    IsOrthonormalBasis e ↔ ∃ b : HilbertBasis ℕ ℝ H, ⇑b = e := by
  constructor
  · rintro ⟨hon, hdense⟩
    exact ⟨HilbertBasis.mk hon (Submodule.dense_iff_topologicalClosure_eq_top.1 hdense).ge,
      HilbertBasis.coe_mk hon _⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b.orthonormal, Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span⟩

/-- **Corollary 5.10.** For an orthonormal basis `(eₙ)` and every `u ∈ H`,
`u = ∑_{k=1}^∞ (u, eₖ) eₖ`, i.e. `u = lim ∑_{k≤n} (u, eₖ) eₖ`, and `|u|² = ∑ |(u, eₖ)|²`. -/
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

/-- **Corollary 5.10, the converse.** For an orthonormal basis `(eₙ)` and a sequence `(αₙ) ∈ ℓ²`,
the series `∑ αₖ eₖ` converges to some `u ∈ H` with `(u, eₖ) = αₖ` for all `k` and
`|u|² = ∑ αₖ²`. No density is needed: an orthonormal sequence suffices. -/
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

/-- **Remark 9.** The series of Corollary 5.10 need not converge absolutely: for every
orthonormal basis `(eₙ)` there is `u ∈ H` with `∑ |(u, eₖ)| = ∞` — the vector with coefficients
`αₖ = 1 / (k + 1)`, square-summable but not summable. The Hilbert-sum form of the remark (the
series `∑ uₖ` of Theorem 5.9) is this one at `Eₖ = ℝ eₖ`. -/
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

/-- **Theorem 5.11.** Every separable Hilbert space has an orthonormal basis: in the form true in
every dimension, a Hilbert basis indexed by a countable subset of `H`. The book proves it by
Gram–Schmidt on a dense sequence; the backbone from Mathlib's `exists_hilbertBasis` and the
countability of orthonormal families in a separable space. -/
theorem theorem_5_11 [TopologicalSpace.SeparableSpace H] :
    ∃ (w : Set H) (b : HilbertBasis w ℝ H), w.Countable ∧ ⇑b = ((↑) : w → H) :=
  exists_hilbertBasis_countable ℝ H

/-- **Theorem 5.11, in the book's form.** A separable infinite-dimensional Hilbert space has an
orthonormal basis that is a sequence `(eₙ)_{n ≥ 1}` (a finite-dimensional space cannot have
one, which is why the dimension hypothesis is added). -/
theorem theorem_5_11_nat [TopologicalSpace.SeparableSpace H] (h : ¬ FiniteDimensional ℝ H) :
    ∃ e : ℕ → H, IsOrthonormalBasis e := by
  obtain ⟨b⟩ := exists_hilbertBasis_nat ℝ H h
  exact ⟨b, (isOrthonormalBasis_iff b).2 ⟨b, rfl⟩⟩

/-- **Remark 10.** All separable infinite-dimensional Hilbert spaces are isomorphic and isometric
to `ℓ²`: the coordinate map of a basis `(eₙ)_{n ≥ 1}`. -/
theorem remark_5_10 [TopologicalSpace.SeparableSpace H] (h : ¬ FiniteDimensional ℝ H) :
    Nonempty (H ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) 2) := by
  obtain ⟨b⟩ := exists_hilbertBasis_nat ℝ H h
  exact ⟨b.repr⟩

/-- **Remark 11.** A nonseparable Hilbert space still has an (uncountable) orthonormal basis
`(eᵢ)_{i ∈ I}`, by Zorn's lemma: Mathlib's `exists_hilbertBasis`. -/
theorem remark_5_11 : ∃ (w : Set H) (b : HilbertBasis w ℝ H), ⇑b = ((↑) : w → H) :=
  exists_hilbertBasis ℝ H

end Brezis.Chapter05

end
