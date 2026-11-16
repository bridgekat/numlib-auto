# Documentation comment structures

This file fixes the structure of doc comments at three levels: the index module of a surface library, every other module, and each declaration. It refines the "Documentation comments rubrics" in [`proof-rubrics.md`](../proof-rubrics.md), which still apply.

Doc comments are published on the [documentation website](https://bridgekat.github.io/numlib-auto/docs/Numlib.html). The reader is a person who wants to learn the mathematics. This reader has not seen the source text, the plans, or any agent's work. Therefore each doc comment must state the mathematics in natural language, and that statement must agree with the Lean code below it.

# Rules for all levels

- **State the mathematics.** A doc comment gives definitions and statements in mathematical prose. A label alone ("Equation (10.21) of the survey", "Helper for `foo`", "Identification with Mathlib") is not a doc comment, because the reader learns nothing from it.
- **Describe the Lean code as it is.** The prose is a translation of the formal statement. Where the formal statement differs from the source, the prose follows the formal statement and records the difference as a deviation (see below).
- **Write mathematics in LaTeX and Lean in backticks.** Use `$…$` inline and `$$…$$` for a displayed formula. Use backticks only for Lean names and Lean expressions. Do not put mathematical notation in backticks. The reader can then tell the mathematical statement from its Lean encoding.
- **Write Lean names fully qualified** (`Matrix.HasPencilEigenvector`, `BenziGolubLiesen.theorem_3_1`), so that the website turns them into links. Refer to a module by its module name (`Numlib.Eigen.Pencil`), not by a file path.
- **Cite at the point of use.** Write `[key]` or `[text][key]` with a key from [`references.bib`](../../references/references.bib). Do not write a `## References` section: the citation is the link.
- **Make the first paragraph stand alone.** The tracker and the search results show the first paragraph without the rest.
- **Use the fixed headings in the fixed order.** Each template below lists them. Omit a section that has no content, unless the template marks it as required. Do not invent other second-level headings.
- **Describe the final state only.** Do not mention the history of the work, agents, plans, notes, or earlier versions. Do not refer to files outside the published library, such as `plans/` or `notes/`.
- **Follow Mathlib layout.** Write full sentences that end with a period. Wrap lines at 100 characters; only a line that Markdown cannot break (a title, a table row, a single Lean name) can be longer. In a module doc comment, put `/-!` and `-/` on their own lines. In a declaration doc comment, start the text on the `/--` line and end it with `-/` on the last line.

# Deviations from the source

A deviation is a difference in meaning between a surface declaration and the item printed in the source. Each deviation has one of four kinds.

| Kind | Meaning |
|---|---|
| **Correction** | The printed statement is false, or cannot be proved as printed. The formal statement changes a hypothesis or the conclusion. |
| **Typo** | The source has a misprint, and the intended meaning is clear. |
| **Reading** | The source is ambiguous or leaves something implicit. The formal statement fixes one interpretation. |
| **Generalization** | The formal statement proves more than the printed one, and the printed one is a special case. |

Record each deviation in three places, and keep the three consistent.

- The declaration doc comment gives the full account: what the source prints, what the declaration states instead, and why. For a correction, give the counterexample or name the declaration that proves it.
- The doc comment of the module that contains the declaration gives one line.
- The doc comment of the library index gives one line.

Record an item that is not formalized in two places: the module where the item would be, and the library index. Give the reason in one sentence.

# Level 1: the index module of a surface library

Each source has one index module `NumlibSurface/<Source>.lean`. It imports all modules of the library and contains only a doc comment. This doc comment is the front page of the library on the website.

## Template

```lean
/-!
# <Authors>, *<Title of the source>*

<Summary, one paragraph. Cite the source as `[key]`, with the edition if it matters. Say what the
source is about, which parts this library formalizes, and which backbone areas supply the proofs.>

## Coverage

<Which kinds of numbered items are formalized (theorems, lemmas, definitions, algorithms, …). How
many of the total are formalized. Which classes of content are out of scope (exercises, numerical
experiments, historical notes, …).>

## Contents

| Source | Module | Subject |
|---|---|---|
| <unit number and title in the source> | `<relative module name>` | <items covered> |

## Conventions

* <Naming: how a declaration name follows from an item number, and how the parts of one item are
  named.>
* <Notation and standing assumptions of the source, each with its Lean counterpart.>

## Deviations from the source

* **<Item>** (<kind>). <What the source prints, and what the library states instead.> See
  `<declaration>`.

## Not formalized

* **<Item>.** <Reason.>
-/
```

All six sections are required. If a library has no deviations or no omitted items, write one sentence that says so. In a large library, group the entries of the last two sections by chapter with bold chapter names. Use the unit names and numbers of the source in the `Source` column ("Part II", "§3.2", "Appendix A"), even when the module is named `ChapterNN`. In the `Module` column, write each module name relative to `NumlibSurface.<Source>`, so that a table row fits in one line.

## Example

```lean
/-!
# Benzi, Golub and Liesen, *Numerical solution of saddle point problems*

This library formalizes the numbered results of the survey [benzi2005numerical]. The survey studies
linear systems whose coefficient matrix has the saddle-point form
$$\mathcal{A} = \begin{bmatrix} A & B_1^T \\ B_2 & -C \end{bmatrix},$$
with $A \in \mathbb{R}^{n \times n}$, $B_1, B_2 \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times m}$. The formalized results give conditions for $\mathcal{A}$ to be
nonsingular, bounds on its spectrum, optimality properties of Krylov subspace methods, and the
spectrum of $\mathcal{A}$ after constraint preconditioning. The proofs specialize backbone results
in `Numlib.LinearAlgebra.Matrix.SaddlePoint`, `Numlib.Krylov` and `Numlib.Preconditioner`.

## Coverage

The survey has 13 numbered results: Theorems 3.1–3.8, 9.1–9.3 and 10.1, and Lemma 10.2. All 13 are
formalized, together with the definitions and equations that their statements use. Applications,
descriptions of solvers and numerical experiments are out of scope.

## Contents

| Source | Module | Subject |
|---|---|---|
| §1 Introduction | `Section01` | the matrix $\mathcal{A}$ of (1.1) |
| §3.2 Solvability conditions | `Section03.Solvability` | Theorems 3.1–3.4 |
| §3.4 Spectral properties | `Section03.Spectrum` | Theorems 3.5–3.8 |
| §9 Krylov subspace methods | `Section09` | Theorems 9.1–9.3 |
| §10.2 Constraint preconditioning | `Section10.Constraint` | Theorem 10.1 |
| §10.2 Constraint preconditioning | `Section10.Pencil` | equation (10.21), Lemma 10.2 |

## Conventions

* Theorem 3.1 is `BenziGolubLiesen.theorem_3_1`, and part (iii) of Lemma 10.2 is
  `BenziGolubLiesen.lemma_10_2_iii`. All declarations are in the namespace `BenziGolubLiesen`.
* Matrices are indexed by finite types: $A \in \mathbb{R}^{n \times n}$ is `A : Matrix n n ℝ`, and
  a block matrix of order $n + m$ is indexed by `n ⊕ m`.
* "$B$ has full rank" for $B \in \mathbb{R}^{m \times n}$ means $\operatorname{rank} B = m$, which
  is `B.rank = Fintype.card m`.
* Eigenvectors are complex. A real matrix acts on complex vectors through `Matrix.complexify`.

## Deviations from the source

* **Remark after Theorem 3.8** (correction). The source calls the nonreal eigenvalues purely
  imaginary. They have real part $\eta / 2$. See `BenziGolubLiesen.signFlipped_roots_re_of_lt`.
* **Theorem 10.1** (correction). The eigenvalue $1$ can have multiplicity greater than $2m$,
  because the reduced pencil can also have the eigenvalue $1$. See
  `BenziGolubLiesen.theorem_10_1`.
* **Lemma 10.2(ii)** (correction). The source requires $y \neq 0$ at the eigenvalue $0$. The
  condition is $Ex = 0$ alone. See `BenziGolubLiesen.lemma_10_2_ii`.
* **Lemma 10.2(iii)** (correction). The source prints the upper bound $\lambda_{\max}(E)$. The
  upper bound is $\max\{0, \lambda_{\max}(E)\}$. See `BenziGolubLiesen.lemma_10_2_iii`.

## Not formalized

All numbered results are formalized.
-/
```

# Level 2: module doc comments

Every module has one module doc comment after its imports. The template is the same for the backbone and the surface. Some sections apply to one layer only.

## Template

```lean
/-!
# <Title>

<Summary, one or two paragraphs. Give the mathematical setting and say what the module defines
and proves, in natural language with the main formulas. Introduce the notation that the lists
below use.>

## Main definitions

* `<Name>`: <the definition in one sentence>.

## Main results

* `<name>`: <the statement in one sentence>.

## Proof outline

<Optional. The mathematical idea of the main proofs, in a few sentences. Do not describe the Lean
steps.>

## Notation

* `<notation>`: <meaning>.

## Conventions

* <Surface only. Notation or standing assumptions of this part of the source, each with its Lean
  counterpart, where they add to the conventions of the library index.>

## Implementation notes

* <Design decisions of the Lean encoding that a reader or user needs: the choice of types, the
  values at degenerate arguments, the `simp` normal form, the relation to Mathlib.>

## Deviations from the source

* <Surface only. Same one-line form as in the library index.>

## Not formalized

* <Surface only. Same one-line form as in the library index.>
-/
```

The title and the summary are required. The rules for the title and the two lists depend on the layer.

| | Backbone module | Surface module |
|---|---|---|
| Title | The mathematical subject, as a noun phrase: `# The primal block pencil`. | The source, the unit and the unit's title: `# Benzi, Golub and Liesen, Section 10.2: Constraint and indefinite preconditioning`. Use the unit name and number of the source. |
| Summary | The setting and the main facts. Cite a source where the module follows one. | Cite the source as `[key]`. Say what this unit of the source covers and which backbone modules supply the proofs. |
| `Main definitions` and `Main results` | A selection: the planned declarations and the declarations that other modules use. | Complete for the numbered items of the unit, in the order of the source. Start each entry with the item label: ``* Theorem 3.1, `BenziGolubLiesen.theorem_3_1`: …``. |

An entry in `Main definitions` or `Main results` is a one-sentence gloss. The complete statement belongs to the declaration doc comment.

A chapter index module, which only imports the section modules of one chapter, has the title, a summary, and one section `## Contents` with the same table as the library index. It does not repeat deviations.

To divide a long file, use sectioning comments with a third-level heading: `/-! ### <Title> -/`. A sectioning comment can have a short paragraph below the heading. Second-level headings appear only in the module doc comment.

## Example

```lean
/-!
# The primal block pencil

This file studies the generalized eigenvalue problem
$$\begin{bmatrix} E & 0 \\ 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix}
  = \gamma \begin{bmatrix} I & B^H \\ B & -C \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix},
  \qquad (x, y) \neq 0,$$
for $E \in \mathbb{C}^{n \times n}$, $B \in \mathbb{C}^{m \times n}$ and
$C \in \mathbb{C}^{m \times m}$. A triple $(\gamma, x, y)$ that satisfies it is called an eigenpair
below. The problem describes the spectrum of a saddle-point matrix after constraint
preconditioning, as in Lemma 10.2 of [benzi2005numerical].

The eigenvalue $\gamma = 0$ puts no condition on $y$. For $\gamma \neq 0$ the second block row
gives $Bx = Cy$, and then $\gamma = x^H E x / (x^H x + y^H C y)$. The denominator is positive when
$C$ is positive semidefinite and $B^H$ is injective.

## Main results

* `Matrix.hasPencilEigenvector_primalBlock_zero_iff`: $(0, x, y)$ is an eigenpair if and only if
  $(x, y) \neq 0$ and $Ex = 0$.
* `Matrix.finrank_ker_fromBlocks_primal`: the kernel of $\operatorname{diag}(E, 0)$ has dimension
  $\dim \ker E + m$.
* `Matrix.HasPencilEigenvector.primalBlock_eq_zero_iff`: if $C$ is positive semidefinite and $B^H$
  is injective, an eigenpair has $\gamma = 0$ if and only if $Ex = 0$.
* `Matrix.HasPencilEigenvector.primalBlock_eq_rayleigh`: if $C$ is positive definite, $B^H$ is
  injective and $Ex \neq 0$, then $\gamma = x^H E x / x^H (I + B^H C^{-1} B) x$ and $\gamma \neq 0$.
* `Matrix.HasPencilEigenvector.primalBlock_mem_interval`: if $C$ is positive semidefinite, $B^H$
  is injective, $E$ is Hermitian with $a \|v\|^2 \le v^H E v \le b \|v\|^2$ for all $v$, and
  $\gamma \neq 0$, then $\gamma$ is real and $\min\{0, a\} \le \gamma \le \max\{0, b\}$.

## Implementation notes

* An eigenpair is `Matrix.HasPencilEigenvector (fromBlocks E 0 0 0) (fromBlocks 1 Bᴴ B (-C)) γ
  (Sum.elim x y)`. Block matrices are indexed by `n ⊕ m`, and the pair $(x, y)$ is `Sum.elim x y`.
* The first two results hold over any field. The first holds for any second matrix of the pencil.
* The bounds $a$ and $b$ on $E$ are stated as `LinearMap.IsSymmetricBoundedBy` for
  `Matrix.toEuclideanLin E`. They need not be eigenvalues of $E$.
-/
```

# Level 3: declaration doc comments

## Level of detail

The required detail depends on the role of the declaration.

| Declaration | Required doc comment |
|---|---|
| A planned declaration: a numbered item of a source, or a key backbone definition or theorem named in a plan under `plans/` | The full form of the template below, with a complete statement. |
| Any other public definition, theorem or instance with mathematical content | The statement or definition in one to three sentences. |
| A structure field | One sentence: what the data is, or what the axiom asserts. |
| A private or auxiliary declaration | Optional. One sentence if present. |

## Template

A full doc comment has up to three paragraphs in this order, with a blank line between them.

```lean
/-- <Label.> <Statement.>

**<Kind of deviation>.** <What the source prints, what is stated here instead, and why.>

<Notes on the encoding.> -/
```

**Label.** The label identifies the item. It is bold.

- A numbered item of a source: `**Theorem 3.1** of [key].` Add a well-known name in parentheses: `**Theorem 5.1.3** of [key] (Banach fixed-point theorem).`
- One part of a numbered item: use the part label of the source, `**Lemma 10.2(iii)** of [key].` If the source has no part labels, name the part in words after the citation: `**Theorem 3.4** of [key], uniqueness.`
- Unnumbered content of a source: name the nearest unit, `**Equation (10.21)** of [key].` or `**Section 3.1** of [key], definition of the weak topology.`
- A backbone declaration has no label. If the theorem has a name, put the name in bold in the first sentence: `The **Banach fixed-point theorem**: …`. A backbone declaration that follows a source can cite it at the end of the statement: `This is Proposition 6.4 of [saad2003iterative].`
- A supporting declaration of the surface that is not an item of the source has no label. Its statement names the item that it supports.

**Statement.** The statement is complete and self-contained mathematical prose.

- For a theorem, introduce every object with its type ("Let $B \in \mathbb{R}^{m \times n}$ …"), then give the hypotheses, then the conclusion. Put the main formula in display math.
- For a definition, give the defining condition or formula, and put the defined term in bold where it is defined. For a structure, say what an element of the structure consists of.
- In the surface, use the wording and the notation of the source. In the backbone, use the notation of the module summary.

The statement must match the Lean code. Compare them item by item before you finish.

- Each hypothesis of the Lean statement appears in the prose, and each hypothesis in the prose appears in the Lean statement. This includes type class assumptions with mathematical content: `[Nonempty n]` is "$n \ge 1$", and `[CompleteSpace E]` is "$E$ is complete". Technical assumptions such as `[DecidableEq n]` do not appear.
- The conclusion has the same strength. An equivalence stays an equivalence, and the order of the quantifiers is the same.
- Degenerate cases agree. If the Lean code gives a value at a degenerate argument (division by zero, an empty index set, the supremum of an unbounded set), the prose says so.
- Where a Lean term is not the obvious counterpart of a symbol, the notes say which Lean term is which symbol.

**Deviation.** This paragraph is present only for a surface declaration that deviates from the source. It starts with the kind in bold: `**Correction.**`, `**Typo.**`, `**Reading.**` or `**Generalization.**`

**Notes.** This paragraph is optional. It tells the reader how the Lean code encodes the statement: which Lean terms stand for which symbols, the index base, the values at degenerate arguments, and the backbone or Mathlib declaration that the proof specializes. For a major theorem, one sentence on the idea of the proof is permitted. Do not describe the steps of the proof.

A short doc comment, for a declaration that is not planned, is the statement paragraph alone.

## Examples

A definition:

```lean
/-- **Equation (10.21)** of [benzi2005numerical]. Let $B \in \mathbb{R}^{m \times n}$,
$C \in \mathbb{R}^{m \times m}$ and $E \in \mathbb{R}^{n \times n}$. A scalar
$\gamma \in \mathbb{C}$ and vectors $x \in \mathbb{C}^n$, $y \in \mathbb{C}^m$ form an
**eigenpair of the constraint pencil** if $(x, y) \neq 0$ and
$$\gamma \begin{bmatrix} I & B^T \\ B & -C \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix}
  = \begin{bmatrix} E & 0 \\ 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix}.$$

The source writes the condition $(x, y) \neq 0$ as $\|x\| + \|y\| \neq 0$. The definition is
`Matrix.HasPencilEigenvector` for the two block matrices, with the real matrices embedded
entrywise in the complex matrices. -/
abbrev IsConstraintPencilEigenvector (B : Matrix m n ℝ) (C : Matrix m m ℝ)
    (E : Matrix n n ℝ) (γ : ℂ) (x : n → ℂ) (y : m → ℂ) : Prop :=
  Matrix.HasPencilEigenvector (fromBlocks E.complexify 0 0 0)
    (fromBlocks 1 (B.map Complex.ofReal)ᴴ (B.map Complex.ofReal) (-C.complexify)) γ (Sum.elim x y)
```

A theorem with a deviation:

```lean
/-- **Lemma 10.2(iii)** of [benzi2005numerical]. Let $B \in \mathbb{R}^{m \times n}$ have rank $m$,
let $C \in \mathbb{R}^{m \times m}$ be symmetric positive semidefinite, and let
$E \in \mathbb{R}^{n \times n}$ be symmetric, with $n \ge 1$. If $(\gamma, x, y)$ is an eigenpair
of the constraint pencil (10.21) and $\gamma \neq 0$, then $\gamma$ is real and
$$\min\{0, \lambda_{\min}(E)\} \le \gamma \le \max\{0, \lambda_{\max}(E)\}.$$

**Correction.** The source prints the upper bound $\lambda_{\max}(E)$. This bound fails when
$\lambda_{\max}(E) < 0$: for $B = C = 1$ and $E = -1$, the pencil has the eigenvalue
$\gamma = -1/2 > -1$. See `BenziGolubLiesen.lemma_10_2_upper_endpoint_example`.

The eigenpair is `BenziGolubLiesen.IsConstraintPencilEigenvector`. The numbers
$\lambda_{\min}(E)$ and $\lambda_{\max}(E)$ are the infimum and the supremum of
`Matrix.IsHermitian.eigenvalues`. The proof specializes
`Matrix.HasPencilEigenvector.primalBlock_mem_interval`. -/
theorem lemma_10_2_iii [Nonempty n] (hB : B.rank = Fintype.card m) (hC : C.PosSemidef)
    (hE : E.IsHermitian) (h : IsConstraintPencilEigenvector B C E γ x y) (hγ : γ ≠ 0) :
    γ ∈ Complex.ofReal '' Set.Icc (min 0 (⨅ i, hE.eigenvalues i))
      (max 0 (⨆ i, hE.eigenvalues i)) := by
```

In the second example, each part of the Lean statement has a counterpart in the prose: `hB` is "rank $m$", `hC` is "symmetric positive semidefinite", `hE` is "symmetric", `[Nonempty n]` is "$n \ge 1$", `h` is "an eigenpair of the constraint pencil", `hγ` is "$\gamma \neq 0$", and the membership in the image of a real interval is "$\gamma$ is real" together with the two bounds.

Short doc comments, for declarations that are not planned:

```lean
/-- A contractivity constant $\alpha$ of a contractive map satisfies $\alpha < 1$. -/
theorem ContractiveOn.lt_one (h : ContractiveOn T K α) : α < 1 := h.2.1

structure Splitting (a : R) where
  /-- The invertible part $m$ of the splitting $a = m - n$. -/
  m : R
```

# Checking

The script [`tools/doc_comments.py`](../../tools/doc_comments.py) supports this standard.

- `python3 tools/doc_comments.py dump <file>` prints a module without proof bodies and marks the planned declarations.
- `python3 tools/doc_comments.py apply <file> <docfile>` replaces or adds doc comments from a text file and wraps them at 100 characters. It refuses any change to the code.
- `python3 tools/doc_comments.py check [<file> …]` verifies that only comments differ from the last commit, and reports violations of the mechanical rules: headings, line length, missing doc comments, and references to files outside the library.
