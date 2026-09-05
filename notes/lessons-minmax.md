# Lessons from `Numlib/Eigen/MinMax`

Written while proving Courant–Fischer and Weyl. Symptom, cause, fix; to be folded into
`lean-lessons.md`.

## Statement design

* **`⨆ _ : P, a` is junk in `ℝ`.** `iSup` over a `Prop` index is `sSup ∅ = 0` when the proposition
  is false, so `⨆ S, ⨆ _ : finrank S = k, f S` silently takes a max with `0` and the theorem is
  false as soon as the eigenvalue is negative. The subtype index
  `⨆ S : {S : Submodule 𝕜 E // finrank 𝕜 S = k}, …` is the only honest spelling. Same for the inner
  `⨅ x ∈ S, ⨅ _ : x ≠ 0, …`. Prove an `IsGreatest`/`IsLeast` over an explicit set of reals first and
  derive the `iSup`/`iInf` from it — the `IsGreatest` form has no junk at all and is what consumers
  should use.
* A set of *bounds* rather than of attained values keeps the `IsGreatest` statement free of an
  inner `sInf`: `{c | ∃ S, finrank S = k ∧ ∀ x ∈ S, x ≠ 0 → c ≤ R x}` is downward closed and its
  greatest element is exactly the max–min value.
* Weyl wants a **hypothesised** bound, not an operator norm: `E →ₗ[𝕜] E` has none, and the weakest
  hypothesis the proof uses is the quadratic-form one,
  `re ⟪A x, x⟫ ≤ re ⟪B x, x⟫ + C ‖x‖ ^ 2`, which is also this library's convention for spectral
  hypotheses. Kress's own proof passes through exactly that inequality. The norm form and the
  `‖A - B‖` form for `E →L[𝕜] E` are two-line corollaries.

## Mathlib route for spans of eigenvectors

* `x ∈ span 𝕜 (b '' ↑s) ↔ ∀ i ∉ s, b.repr x i = 0` is three lemmas:
  `Module.Basis.mem_span_image` on `b.toBasis`, `Finsupp.support_subset_iff`, and
  `OrthonormalBasis.coe_toBasis_repr_apply`. Not a `span_induction`.
* `finrank 𝕜 (span 𝕜 (b '' ↑s)) = s.card` is `Set.image_eq_range` then `finrank_span_eq_card`, with
  linear independence from `b.orthonormal.linearIndependent.comp _ Subtype.val_injective`.
* **The orthogonal complement is avoidable.** "`x` is orthogonal to the first `i` eigenvectors" is
  `∀ j < i, ⟪b j, x⟫ = 0`, which is membership in `span {b j | i ≤ j}` after one
  `simp only [Finset.mem_Ici, not_le, OrthonormalBasis.repr_apply_apply]`. Rayleigh's recursive
  characterization needs no `Kᗮ` API at all, so the missing
  `x ∈ (span 𝕜 s)ᗮ ↔ ∀ u ∈ s, ⟪u, x⟫ = 0` never comes up.
* `Fin.card_Iic : #(Finset.Iic i) = i + 1` and `Fin.card_Ici : #(Finset.Ici i) = n - i` are what
  make the dimension count `(i + 1) + (n - i) > n` an `omega` after `have := i.isLt`.

## Tactic and name traps

* `refine (IsGreatest.csSup_eq ⟨…, ?_⟩).symm` fails with *"Invalid `⟨...⟩` notation: The expected
  type of this term could not be determined"* — the set argument is not determined by the goal,
  because `iSup f` is `sSup (Set.range f)` only up to unfolding. Pass it:
  `IsGreatest.csSup_eq (s := Set.range fun S : … => …)`. With the set pinned, `.symm` closes an
  `⨆`-goal directly, since `iSup f = sSup (Set.range f)` is `rfl`.
* **`gcongr` does not see through a reducible `abbrev`.** On
  `A.rayleighQuotient x ≤ B.rayleighQuotient x` it reports "gcongr did not make progress" even
  though the goal is reducibly `_ / ‖x‖ ^ 2 ≤ _ / ‖x‖ ^ 2`. Apply the lemma by name:
  `div_le_div_of_nonneg_right (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c` (not `div_le_div_right`).
* `RCLike.conj_mul z : conj z * z = (↑‖z‖) ^ 2` puts the coercion *inside* the power, so
  `RCLike.re_ofReal_mul` does not match; insert `← RCLike.ofReal_pow` first.
* `rw [LinearMap.sub_apply] at h1` also unfolds `(A - B) x` inside `‖(A - B) x‖`. A sibling
  hypothesis that still has the folded form then reads as a different atom and `linarith` fails
  with no hint; rewrite both.
* `sub_le_iff_le_add'` is `a - b ≤ c ↔ a ≤ b + c`; the unprimed one gives `a ≤ c + b`.
* `ContinuousLinearMap.coe_sub` is deprecated in favour of `ContinuousLinearMap.toLinearMap_sub`.
* `Module.finrank_pos_iff` gives `Nontrivial` of the subtype, and `exists_ne (0 : ↥(S ⊓ W))` then
  produces the nonzero intersection vector; `Submodule.mem_inf` is `Iff.rfl`, so `hx.1`/`hx.2`
  work on the membership without a rewrite.

## Structure

* `include hT` in the one-operator section, and a **second `namespace` block** without it for the
  two-operator theorems (Weyl, monotonicity). Otherwise `hT` rides along on statements about
  `A` and `B` — the trap already recorded in `lean-lessons.md`.
* `Numlib/Eigen/Perturbation.lean` carries **private** copies of the two eigenbasis expansions
  (`sum_norm_repr_sq`, `re_inner_apply_self`). `MinMax` needs them too and cannot see them, so it
  has public ones (`norm_sq_eq_sum_norm_repr_sq`, `re_inner_apply_self_eq_sum`). Perturbation's
  privates could be deleted in favour of these if the import direction is ever reversed.

## On the plan's estimate

The plan budgeted "~100 lines with `Submodule.finrank_sup_add_finrank_inf_eq`" for Courant–Fischer.
The dimension count really is four lines, and each of the four directional lemmas is six; what the
estimate missed is that the reusable part is the *`eigenvectorSpan` API* — membership, dimension,
and the two quadratic-form bounds over an arbitrary `s : Finset (Fin n)` — after which max–min,
min–max, Rayleigh's recursive form, monotonicity and Weyl are each under fifteen lines. Build the
span API first and the four theorems fall out; write them one at a time and the dimension count
gets repeated four times.
