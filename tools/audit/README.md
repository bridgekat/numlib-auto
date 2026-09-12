# audit

Reads a Lean project's compiled library and reports what a refactor should look at. Where the
tracker (`tools/tracker`) answers *what is proved*, this answers *what is unused, what is
duplicated, and what the surface never asks for* — questions that a regex over source cannot
answer, because they are about elaborated terms and the reference graph, not text.

Everything is read off the environment. A *use* is a reference in a type or a proof term; a
*statement* is an expression up to binder names and universe levels. A mention in a doc comment is
not a use; a lemma with its binders permuted is not a match.

## Run it

```
lake build                       # it reads oleans, so build first
lake exe audit modules           # backbone modules nothing else imports
lake exe audit unreached         # backbone declarations no surface reaches, even transitively
lake exe audit dead              # declarations with no consumer at all
lake exe audit dups              # pairs of project theorems with the same statement
lake exe audit mathlib           # project theorems whose statement is already in Mathlib (slow)
lake exe audit all
```

`--under PREFIX` restricts any report to one module prefix; `--from A,B` sets the consuming
libraries for `unreached` (default: every root whose name ends in `Surface`); `--roots A,B`
overrides the `lean_lib` names read from `lakefile.toml`.

Importing the project takes about a minute. `mathlib` additionally indexes every imported theorem
and takes several.

## Reading the reports

**Each report is a list of candidates, not a verdict.** The tool says where to look; the build and
the plan adjudicate.

* **`unreached` is the README's own criterion applied mechanically.** The backbone is meant to be
  *driven by demands from the surface*, so a backbone declaration that no surface reaches — even
  through a chain of other backbone lemmas — is one the surface has not asked for. Two readings are
  possible and the tool cannot tell them apart: a module built ahead of a surface that has not been
  written yet (check whether its module doc cites a book with no surface library), or a leftover.
  A *whole module* in this report is the case worth a decision.
* **`dead` is broader and noisier.** Most hits are terminal API: the theorem at the top of a
  module, used by a surface and by nothing else. Use it with `--under` on one module, not globally.
* **`dups` needs sorting by layer.** A surface node with the same statement as its backbone
  original is a *delegating restatement* and is by design — `CONTRIBUTING.md` permits exactly that.
  The hits that matter are **surface ↔ surface** (a later chapter reproved what an earlier one
  restated, against the forward-dependency rule) and **backbone ↔ backbone** (a true duplicate).
* **`mathlib`** should be nearly empty, and a surface node restating a Mathlib theorem under the
  book's number is fine. A *backbone* hit is a lemma to delete.

## What it deliberately does not do

**There is no report on unused instance binders.** Whether a proof needs `[CompleteSpace V]` is
decided by typeclass resolution *during elaboration*, and the compiled term records that in no
form the environment can check: an instance consumed by `fromCompletion` need not leave the
binder's free variable in the value, and the class constant need not appear either, since the term
goes through projections. Two formulations were tried — `containsFVar` on the value, and
occurrence of the class name anywhere in the term — and both produced false positives in bulk
(772 and 4576 declarations, the first checked by hand being a genuinely required binder). The only
sound test is to delete the binder and let the build decide.

For *conflicting* instance binders — `[NormedSpace 𝕜 E]` beside `[InnerProductSpace 𝕜 E]`, an
instance diamond — Mathlib's `linter.overlappingInstances` already fires at build time, is on by
default, and is clean on this project. Do not re-implement it.

## Structure

`Audit/Env.lean` imports the project and filters constants to the ones a person wrote (`isUserDecl`
rejects equation lemmas, `match_` and `proof_` helpers, projections, recursors). `Audit/Dead.lean`
builds the use graph and answers `dead`, `modules` and `unreached`. `Audit/Duplicates.lean` hashes
canonical types for `dups` and `mathlib`. `Main.lean` is the command line.

A trap the first version fell into, recorded so it is not repeated: **a declaration's namespace need
not match its module.** `FloatingPoint.foo` lives in `Numlib.FloatingPoint`. Every filter here
selects by *module* (`moduleOf`), never by name prefix; a name-prefix filter on `Numlib` silently
selects nothing from such modules and reports zero.
