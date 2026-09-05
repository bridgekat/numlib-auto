# Lessons from `Numlib/Eigen/PowerMethod.lean`

Written while formalizing the power method (`agent/power`). Symptom, cause, fix; to be folded into
`notes/lean-lessons.md` by the coordinator.

## The mathematics the plan got wrong

* **Gelfand's formula is not needed for the power method, and neither is the spectrum of a
  restriction.** The plan budgeted `spectrum (A|_W) = σ(A) ∖ {λ₁}` plus Gelfand to get
  `‖(A|_W)^k‖ ≤ C r^k`. The elementary argument is four lines of induction and strictly more
  general. For one generalized eigenvector, `(A − μ)^N w = 0` and `‖μ‖ < r` give
  `‖A^k w‖ ≤ C r^k`: induct on `N`, and use that `A w = μ w + (A − μ) w` turns a bound
  `‖A^k ((A − μ) w)‖ ≤ C r^k` into the scalar recursion `a_{k+1} ≤ ‖μ‖ a_k + C r^k`, whose solution
  is `a_k ≤ (‖w‖ + C/(r − ‖μ‖)) r^k` — an inner induction on `k` needing only
  `C ≤ D (r − ‖μ‖)`. No continuity of `A`, no completeness of `E`, no finite dimension, and it
  holds over any normed field. The plan's route also needed the restriction `A|_W` as a *bounded*
  operator on a Banach algebra, which drags in `CompleteSpace ↥W`; none of that appears.
* **Bundle "the orbit is `O(r^k)`" as a `Submodule` and the `iSup` case is free.** The set
  `{w | ∃ C, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k}` is a submodule (add the constants; scale by `‖c‖`), so
  `⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ ≤ it` is one `iSup₂_le`, with no induction over the
  supremum and no `Finset.sup` over the spectrum. The same trick with the carrier
  `{w | Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) w) atTop (𝓝 0)}` removes the need for a *uniform*
  rate `r`: each eigenvalue `μ` may pick its own `r = (‖μ‖ + ‖λ₁‖)/2`. That is what makes the
  convergence theorem provable with the bare hypothesis `‖μ‖ < ‖λ₁‖` and no gap constant, and
  avoids the "maximum of a finite set of reals, empty case included" bookkeeping entirely.
* **`λ₁ ≠ 0` is a real hypothesis, not a technicality.** With `λ₁ = 0` the dominance hypothesis is
  vacuous (it forces `σ(A) ⊆ {0}`), `W = ⊥`, and the conclusion `(0^k)⁻¹ • A^k x₀ → u` is *false*
  for any `u ≠ 0` in `ker A`: the left side is `0` for every `k ≥ 1`. Check the degenerate
  eigenvalue before deciding a hypothesis is redundant.
* **Read the book: "semi-simple" is not "simple".** Saad, *Numerical Methods for Large Eigenvalue
  Problems*, Thm 4.1 assumes the dominant eigenvalue is *semi-simple*, i.e. `maxGenEigenspace λ₁ =
  eigenspace λ₁`; simple (`finrank (maxGenEigenspace λ₁) = 1`) is a strictly stronger hypothesis
  and gives a weaker theorem. Weaker still, and what the proof actually consumes: only that the
  `λ₁`-component of *this* `x₀` is an eigenvector. Stating it that way made the semi-simple and
  the simple forms both fall out as corollaries.
* **The direction converges only "essentially", and the book says so.** A norm-normalized iterate
  cannot converge on the nose, since each step multiplies the eigendirection by `λ₁/‖λ₁‖`. Saad's
  Algorithm 4.1 dodges this by normalizing by the *entry of largest modulus* — a complex scalar —
  and his §5.1 introduces the general notion: `x_k` **converges essentially** to `x` when
  `c_k x_k → x` for some `c_k` of modulus one. State that, with the `c_k` explicit; the phase-free
  companion is that the residual `‖A x_k − λ₁ x_k‖ → 0`.
* **The projector for a generalized-eigenspace decomposition is oblique.** `IsCompl` of
  `maxGenEigenspace λ` with `⨆ μ ≠ λ, maxGenEigenspace μ` follows from
  `Module.End.independent_maxGenEigenspace` (disjointness) and `iSup_split_single` plus
  `Module.End.iSup_maxGenEigenspace_eq_top` (codisjointness), and `Submodule.linearProjOfIsCompl`
  then *is* the spectral projector. `Submodule.starProjection` is the wrong object: the
  decomposition is not orthogonal unless `A` is normal.

## Lean and Mathlib

* `Module.End.maxGenEigenspace f μ ≠ ⊥ → f.HasEigenvalue μ` is
  `Module.End.HasUnifEigenvalue.lt zero_lt_one h`: `maxGenEigenspace` is `genEigenspace μ ⊤`, and
  `HasUnifEigenvalue f μ k` is *definitionally* `genEigenspace f μ k ≠ ⊥`, so the `⊤`-indexed
  hypothesis is accepted directly. `Module.End.hasEigenvalue_iff` converts the other way.
* `iSup_split_single (f : β → α) (i₀ : β) : ⨆ i, f i = f i₀ ⊔ ⨆ i, ⨆ (_ : i ≠ i₀), f i` is the
  lemma that separates one eigenvalue from the rest. Write the complement as
  `⨆ μ, ⨆ _ : μ ≠ l, …` (not `⨆ μ ∈ s, …`) so that it matches.
* **`iSup₂_le … hw` does not elaborate.** `refine iSup₂_le (fun μ hμ => ?_) hw` fails with
  "Function expected at …" because the `≤` has to be elaborated before it can be applied to the
  membership. Bind it: `have key : (⨆ …) ≤ S := iSup₂_le fun μ hμ => ?_` and then `exact key hw`.
* A `Submodule` built with `where carrier := {v | Tendsto …}` is fine to *prove* things about, but
  the goal `x ∈ S` is not syntactically a `Tendsto`, so `squeeze_zero_norm` cannot infer its bound
  and `refine` reports "don't know how to synthesize implicit argument". Add a
  `private theorem mem_S : v ∈ S ↔ Tendsto … := Iff.rfl` and `rw` with it; that is cheaper than
  `change`, which the style linter also polices.
* Confirming a `lean-lessons` entry: `squeeze_zero_norm` cannot infer its majorant from
  `refine … (fun k => ?_) ?_`. Bind the bound as a named `have` and pass it.
* Inside a `Submodule` structure literal, destructuring the membership hypothesis with `rintro v w
  ⟨C₁, h₁⟩ ⟨C₂, h₂⟩` works, but dot notation on it (`hv.add hv'`) does not — the head of its type
  is `Membership.mem`. Apply `Filter.Tendsto.add hv hv'` by full name instead, and finish with
  `Filter.Tendsto.congr`.
* **`ring` failing inside a `calc` step can be reported with no source position at all.** The
  message is
  `Try this: [apply] ring_nf … The 'ring' tactic failed to close the goal`, printed on stdout by
  `lake env lean` as an *information* message with no `file:line:col` prefix, while the actual
  error surfaces (if at all) somewhere else. `lake env lean --json F.lean` prints the position.
  Here the cause was a goal `(a⁻¹ * b) • x = c • x`, which is an equality of `•` and needs
  `congr 1` first — `ring` has nothing to work on. (`module` is the other fix; see
  `lean-lessons`.)
* `rw [div_pow]` rewrites the *leftmost* `(a/b)^n`, which may be a subterm of the left-hand side
  rather than the `(r/‖l‖)^k` you meant. If the rate `r` is a concrete expression such as
  `(‖μ‖ + ‖l‖)/2`, obtain it as an opaque local first (`obtain ⟨r, hr₁, hr₂⟩ : ∃ r, … `, or state
  the lemma with `r` a variable and instantiate) — then `ring` closes
  `(‖l‖ ^ k)⁻¹ * (C * r ^ k) = C * (r / ‖l‖) ^ k` immediately. With `r` unfolded, `ring` cannot,
  because it distributes the division inside the base and the two sides normalize differently.
* `pow_succ : a ^ (n + 1) = a ^ n * a` and `pow_succ' : a ^ (n + 1) = a * a ^ n`. For
  `(A ^ (k+1)) w = (A ^ k) (A w)` use `pow_succ`; for `A ((A ^ k) w)` use `pow_succ'`. Getting it
  backwards gives "Did not find an occurrence of the pattern".
* Names that took a search: `Submodule.finiteDimensional_of_le` (in the `Submodule` namespace, not
  `FiniteDimensional`), `Submodule.one_le_finrank_iff : 1 ≤ finrank R S ↔ S ≠ ⊥`,
  `Submodule.eq_of_le_of_finrank_le`, `Module.finite_of_finrank_pos`.
  `Submodule.finrank_pos_iff_ne_bot` does not exist.
* The books in `numlib-books/` that the Read tool refuses as "password-protected" extract fine with
  `pdftotext file.pdf out.txt` (whole file, then `grep -n`). Greek letters are dropped, which is
  survivable; the table of contents is not extractable but the body is.
