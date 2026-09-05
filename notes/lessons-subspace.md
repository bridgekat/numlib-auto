# Lessons from subspace iteration in `Numlib/Eigen/PowerMethod.lean`

Written while closing the last open node of `Eigen/PowerMethod` (`agent/subspace`). Symptom,
cause, fix; to be folded into `notes/lean-lessons.md` by the coordinator.

## Reading the books

* **One paraphrase collapsed two different theorems.** The node was planned as
  `subspaceIterate_gap_le`. Saad, *Numerical Methods for Large Eigenvalue Problems*, Thm 5.2 is
  *not* a gap statement: it bounds `‖(I − P_k) u_i‖`, the distance from one dominant eigenvector to
  `S_k = A^k S₀`, and it is per-eigenvector. But **Kress, *Numerical Analysis*, Lemma 7.18 is** the
  gap statement, `‖P_{A^k S} − P_T‖ ≤ M |λ_{m+1}/λ_m|^k` for diagonalizable `A`, and Kress's
  Thm 7.19 (orthogonal iteration) and Thm 7.20 (QR) rest on it. Both books are in the corpus and
  the plan named both under one item. Check every book the plan cites for an item, not the first
  one: the "same" result can be two results of different strength.
* **I nearly recorded a wrong obstruction, and only reading the second book stopped it.** Having
  proved Saad's version, I wrote up the gap form as blocked on four things — a uniform decay
  estimate on the discarded invariant subspace, decay of `(A|_M)^{−k}`, Saad's (3.8)
  `‖P_K − P_L‖ = max {‖(1 − P_K)P_L‖, ‖(1 − P_L)P_K‖}`, and the equality of the two one-sided gaps.
  That list is a *valid route* and it is the wrong one. Kress's own proof needs none of the four:
  it applies the per-vector decay to the `m` vectors of one basis and then compares the two
  projections through their normal equations. The single missing brick is a quantitative continuity
  of the projector in its spanning family, `‖w_j − x_j‖ ≤ δ ⟹ ‖P_{span w} − P_{span x}‖ ≤ M δ`.
  Four of the nine entries in `notes/open-obligations.md` are wrong diagnoses; this would have been
  the fifth. **Before writing an obstruction, read the proof of the theorem you are declaring
  blocked, not the proof of the theorem you just finished.**
* Kress's *display equations are images in the scan*. `pdftotext`, with or without `-layout`, drops
  the inequality of Lemma 7.18 entirely while keeping every word around it. The statement is
  recoverable from the prose (`the orthogonal projections … satisfy [gap] for some constant M; i.e.
  the subspaces `A^ν S` converge to `T`") and from the proof's last line, and the record should say
  the display itself was not read. Saad's PDF loses Greek letters and subscripts but keeps the
  display's shape; Kress's loses the whole display. The two failure modes are different.

## The mathematics the plan overestimated, again

* **One candidate vector replaces the whole gap/angle apparatus.** `‖u − P_{S_k} u‖` is a *minimum*
  over `S_k`, so any single element of `S_k` bounds it. Take `y = λ^{-k} A^k s` for the `s ∈ S₀`
  with `P s = u`: then `y − u = λ^{-k} A^k (s − u)`, which the power method's decay estimate
  already bounds. That is the entire analytic content of Saad Thm 5.2, and the resulting lemma
  (`norm_sub_starProjection_subspaceIterate_le`) mentions no spectrum, no projector, and no finite
  dimension of the ambient space. The plan had budgeted Gelfand's formula *and* a gap API for this;
  it needed neither. Two agents in a row have now found the elementary argument shorter than the
  planned infrastructure — treat the difficulty column as an upper bound only.
* **The spectral projector was already in Mathlib, twice over.** `Submodule.projection p q h` is the
  oblique projector *as an endomorphism* `E →ₗ[R] E`, with `ker_projection`, `range_projection`,
  `isIdempotentElem_projection`, `projection_apply_mem`, `sub_projection_mem`,
  `projection_apply_of_mem_left`, `projection_apply_eq_zero_iff` and
  `projection_add_projection_eq_self` all supplied. `Submodule.projectionOnto` is the version
  landing in the subtype. `Submodule.linearProjOfIsCompl`, which the plan named, is **deprecated**
  (2026-05-04) in favour of `projectionOnto`. Building `Krylov.spectralProjector` was therefore one
  `def` and eight one-line specializations.
* **"P is injective on S₀" is `Disjoint S₀ W`.** Saad states the hypothesis of Thm 5.2 as the
  linear independence of `P x₁, …, P x_m` for a spanning family of `S₀`. Since `ker P = W`, that is
  exactly `Disjoint S₀ W`, which is far easier to supply and to reason with; the equivalence is
  four lines (`injOn_spectralProjector_iff`). Existence of the preimage then comes from rank–nullity
  plus `Submodule.eq_of_le_of_finrank_le`, not from any basis manipulation.

## Mathlib names and API

* `iSup_split (f : β → α) (p : β → Prop) : ⨆ i, f i = (⨆ i, ⨆ _ : p i, f i) ⊔ ⨆ i, ⨆ _ : ¬ p i, f i`
  is the predicate analogue of `iSup_split_single`, and gives codisjointness of a spectral
  splitting for a *set* of eigenvalues by the same one-line `rw` as for a single one.
* Disjointness of the two halves is `iSupIndep.disjoint_biSup_biSup`, which lives in
  `Mathlib/Order/CompactlyGenerated/Basic.lean` and needs `[IsModularLattice α]` plus compact
  generation — both instances for `Submodule`. The primed `iSupIndep.disjoint_biSup_biSup'` in
  `Order/SupIndep.lean` additionally wants `s.Finite`; you do not want that one. Supplying
  `(s := {μ | p μ}) (t := {μ | ¬ p μ})` matches `⨆ i ∈ s, f i` against `⨆ μ, ⨆ _ : p μ, f μ`
  with no rewriting: `i ∈ {μ | p μ}` and `p i` are the same term.
* `iSup_iSup_eq_left` turns `⨆ μ, ⨆ _ : μ = l, f μ` into `f l`, so the one-eigenvalue `IsCompl`
  is `rwa [iSup_iSup_eq_left] at h` from the predicate one. Deriving it that way is two lines and
  removes a duplicated proof.
* `LinearMap.map_le_range`, not `Submodule.map_le_range` — it sits in
  `Mathlib/Algebra/Module/Submodule/Range.lean` but in the `LinearMap` namespace.
* `LinearMap.injOn_of_disjoint_ker (h : s ⊆ p) (hd : Disjoint p (ker f)) : Set.InjOn f s`; pass
  `le_refl (S : Set V)` for `h`.
* `LinearMap.finrank_range_add_finrank_ker` is the rank–nullity to use when the map is
  `f ∘ₗ S.subtype`; combined with `LinearMap.range_comp` and `Submodule.range_subtype` it gives
  `finrank (S.map f) = finrank S` for an `f` injective on `S` without ever building an equiv.
* `Module.End.one_eq_id` and `Module.End.mul_eq_comp` are what let `Submodule.map_id` and
  `Submodule.map_comp` fire on `S.map (A ^ 0)` and `S.map (A ^ (k + 1))`. Without them
  `rw [Submodule.map_comp]` reports "Did not find an occurrence of the pattern
  `Submodule.map (?g ∘ₛₗ ?f) ?p`" against a goal that visibly contains `Submodule.map (A * A ^ k)`.
* `isBestApprox_starProjection K u |>.2 y hy : ‖u − K.starProjection u‖ ≤ ‖u − y‖`, from this
  project's `Numlib.Approximation.BestApprox`, is the usable form of projection minimality.
  Mathlib's `Submodule.starProjection_minimal` is an equation with a `⨅` and needs `ciInf_le` plus
  a `BddBelow` witness at every use.
* The instance chain `[FiniteDimensional 𝕜 ↥S] → FiniteDimensional 𝕜 ↥(S.map f) → CompleteSpace →
  HasOrthogonalProjection` is fully automatic, so `(S.map (A ^ k)).starProjection` elaborates with
  no help and the whole subspace-iteration bound needs no completeness of the ambient space.

## Traps

* **`Module.finrank K (⨆ μ, …)` does not elaborate.** The error is
  `failed to synthesize SupSet (Type u_2)` — the elaborator tries to read the `iSup` at the type
  level rather than inserting the `↥` coercion, which it *does* insert for a named submodule.
  Write `Module.finrank K ↥(⨆ μ, ⨆ _ : p μ, B.maxGenEigenspace μ)` explicitly.
* Confirming an existing lesson: `set M := ⨆ μ, …` and then `rw [← range_spectralProjector]` fails,
  because the goal shows `M` and the lemma produces the `iSup`. Write the supremum out in full;
  it is verbose but it rewrites.
* `heq ▸ hu` where `heq : S.map P = M` and the target is `∃ s ∈ S, P s = u` is rejected with
  "expected result type … does not contain the expected result type on either the left or the right
  hand side". Go through the membership instead: `Submodule.mem_map.mp (heq.ge hu)`.
* `Submodule.projection_apply_eq_zero_iff` takes *only* the `IsCompl` argument; writing
  `Submodule.projection_apply_eq_zero_iff _ _` gives "Function expected at …". Several of its
  neighbours take the point as well, so check each one.
* `u + (s − u) = s` is `add_sub_cancel` in this toolchain (not `add_sub_cancel'` or
  `add_sub_cancel_left`).
* **Shadowing the file's variable block is necessary and dangerous.** `PowerMethod.lean` opens with
  `variable {𝕜 E} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]`, and
  `InnerProductSpace 𝕜 E` extends `NormedSpace 𝕜 E`, so adding the inner-product instance to the
  same block would be a diamond. A new `section` with fresh `{𝕜 E}` variables is the fix — but the
  outer `variable (A : Module.End 𝕜 E)` is still in scope and now refers to the *shadowed* types,
  so a bare `A` in the new section resolves to it and every statement mentioning it goes wrong in a
  way the error message does not explain. Redeclare `A` (and any other data variable) in the new
  section.
