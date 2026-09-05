# The plan

The plan of the library, in the TOML that [tracker](https://github.com/bridgekat/tracker/) reads.
One file per group, and a group is the plan for one module.

```
lake build                  # the tracker reads oleans and never builds, so build first
lake exe tracker status     # counts per group, rolled up through parents
lake exe tracker lint       # plan errors, cycles, placement and kind mismatches
lake exe tracker show <group | id>
lake exe tracker graph --under <group> [--dot]
```

Every command resolves the plan against the compiled library first when the cache is stale, so
`check` is only needed to do that step alone or, with `--force`, to redo it. An edit that has not
been built is invisible to the tracker, which is why `lake build` comes first.

## What a node is

**A node is a result the library stands behind, not every declaration it contains.** The library
writes some three thousand public declarations; this plan names about a thousand of them, by two
rules:

* In the backbone, the nodes are the items the design notes name — the definitions and theorems
  `backbone.md` proposes, at the names it proposes them under. That document is the record of what
  the layer is *for*, so what it names is what the layer promises.
* In a surface, the nodes are the book's numbered results and the definitions the surface
  introduces for the book's vocabulary. Where the library states one numbered result as several
  declarations — its separate clauses, its CG and its MINRES form, a strict beside a nonstrict
  version — each is a node.

What is left out is the working material: intermediate lemmas, `simp` companions, variant forms.
Leaving it out costs nothing, because the tracker reads a proof's real dependencies straight
through untracked constants of the project, so an edge from node to node is drawn whether or not
the proof passed through helpers on the way.

Surface nodes carry no `source` field, unlike some plans, because the name already is one: a
surface declaration is named for the result it states, so `theorem_6_29` in
`NumlibSurface/SaadSparse/Chapter06/Section11` is Saad's Theorem 6.29 and nothing else. The group's
path says which book; the name says which result.

Almost everything here is proved, so the nodes carry nothing but their ids: kind, description and
dependencies are superseded by the declaration, its doc comment and its proof. The exceptions are
the open nodes of the phase-2 eigenvalue modules, which are plans for declarations that do not
exist yet and so carry `kind`, `desc` and `deps` until they do.

## Shape

A group *is* a module, named by the module's path, so this directory is a copy of the source tree
with `.lean` replaced by `.toml`: `tracker/Numlib/Krylov/CG.toml` is the plan for
`Numlib.Krylov.CG`, and the group is `Numlib/Krylov/CG`. That name is the whole of the
correspondence — there is no field pointing at the module — and `lint` reports a declaration that
lands in a module other than its group's.

There are two roots, `Numlib` and `NumlibSurface`, because the project is two Lake libraries and
each has its own module tree. `check` imports the `lean_lib` names of `lakefile.toml`, so a new
library becomes a new root by being registered there and nowhere else.

The split is the layering. A surface depends on the backbone and never the other way round, and
`graph` shows that as a one-way flow — but since the move to two libraries the direction is no
longer only a convention the graph displays: `Numlib` cannot import `NumlibSurface`, and Lake
refuses the attempt. What the plan still adds is the finer claim, which no build system can check:
a surface node whose real dependencies include no backbone node is a surface proof that did not
specialize anything, which is what the README forbids.

A group standing for a module that is only a directory — `Numlib/Krylov`, the chapter directories of
each book — has no nodes, and exists to roll counts up and to carry a description of what the
directory is for. Those descriptions are the only ones the plan writes: every other group has a real
module whose `/-! … -/` doc comment describes it, and a plan copy would only be superseded. Both
roots are of that second kind, so `Numlib.toml` and `NumlibSurface.toml` are empty files, kept
because a directory must have its group file beside it.

A group is addressed by its path or by an unambiguous trailing part of it, so `tracker show
Krylov/CG` works, but `tracker show CG` does not — three modules end in `CG`.

## The prose beside it

The `.md` files here are the reasoning the TOML cannot hold. `backbone.md` is the design record of
the general layer: the corpus it serves, the generality ladder that decides where each item sits,
the named hypothesis bundles, the phasing, and the difficult-proof index. One file per book holds
the surface's book alignment — which numbered result maps to which declaration, how each
book-specific definition relates to the backbone, what was deferred and why.

Where those documents quote a Lean statement, the source is the authority and the document is the
one that is wrong. They are kept because the *arguments* in them — why a theorem is stated over
Banach spaces rather than ℝⁿ, why the spectral hypotheses are quadratic-form bounds — are what no
tool can recover from a compiled environment.

## Building on it

A later project appends its own groups — a backbone one, or a surface per book under
`NumlibSurface` — one per module it intends to write, and names ids from these groups in the
`deps` of its open nodes. `tracker show <id>` then prints the signature the new work has to meet,
and `tracker ready` lists the modules that can be worked on now, never one whose dependencies here
are unproved. Only `Numlib` is tracked, so Mathlib and core never appear as nodes.

Do not restate an existing node under a new name. If a new project needs to depend on something the
library has but this plan does not name, add the node to the group that owns it — that is the plan
admitting the declaration is API.
