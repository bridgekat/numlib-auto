import NumlibSurface.Brezis.Chapter01.Section01
import NumlibSurface.Brezis.Chapter01.Section02
import NumlibSurface.Brezis.Chapter01.Section03
import NumlibSurface.Brezis.Chapter01.Section04
import NumlibSurface.Brezis.Chapter02.Section01
import NumlibSurface.Brezis.Chapter02.Section02
import NumlibSurface.Brezis.Chapter02.Section03
import NumlibSurface.Brezis.Chapter02.Section04
import NumlibSurface.Brezis.Chapter02.Section05
import NumlibSurface.Brezis.Chapter02.Section06
import NumlibSurface.Brezis.Chapter02.Section07
import NumlibSurface.Brezis.Chapter03.Section01
import NumlibSurface.Brezis.Chapter03.Section02
import NumlibSurface.Brezis.Chapter03.Section03
import NumlibSurface.Brezis.Chapter03.Section04
import NumlibSurface.Brezis.Chapter03.Section05
import NumlibSurface.Brezis.Chapter03.Section06
import NumlibSurface.Brezis.Chapter03.Section07
import NumlibSurface.Brezis.Chapter04.Section01
import NumlibSurface.Brezis.Chapter04.Section02
import NumlibSurface.Brezis.Chapter04.Section03
import NumlibSurface.Brezis.Chapter04.Section04
import NumlibSurface.Brezis.Chapter04.Section05
import NumlibSurface.Brezis.Chapter05.Section01
import NumlibSurface.Brezis.Chapter05.Section02
import NumlibSurface.Brezis.Chapter05.Section03
import NumlibSurface.Brezis.Chapter05.Section04
import NumlibSurface.Brezis.Chapter06.Section01
import NumlibSurface.Brezis.Chapter06.Section02
import NumlibSurface.Brezis.Chapter06.Section03
import NumlibSurface.Brezis.Chapter06.Section04
import NumlibSurface.Brezis.Chapter07.Section01
import NumlibSurface.Brezis.Chapter07.Section02
import NumlibSurface.Brezis.Chapter07.Section03
import NumlibSurface.Brezis.Chapter07.Section04
import NumlibSurface.Brezis.Chapter08.Section01
import NumlibSurface.Brezis.Chapter08.Section02
import NumlibSurface.Brezis.Chapter08.Section03
import NumlibSurface.Brezis.Chapter08.Section04
import NumlibSurface.Brezis.Chapter08.Section05
import NumlibSurface.Brezis.Chapter08.Section06
import NumlibSurface.Brezis.Chapter09.Section01
import NumlibSurface.Brezis.Chapter09.Section02
import NumlibSurface.Brezis.Chapter09.Section03
import NumlibSurface.Brezis.Chapter09.Section04
import NumlibSurface.Brezis.Chapter09.Section05
import NumlibSurface.Brezis.Chapter09.Section07
import NumlibSurface.Brezis.Chapter11.Section01
import NumlibSurface.Brezis.Chapter11.Section02
import NumlibSurface.Brezis.Chapter11.Section03
import NumlibSurface.Brezis.Chapter11.Section04

/-!
# Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*

The surface library for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial
Differential Equations*, Universitext, Springer, 2011 [brezis2011functional]: one module per
section of the book, `ChapterNN.SectionMM` in the namespace `Brezis.ChapterNN`. Each states the
book's results in the book's own terms and proves them from Mathlib and the general backbone
`Numlib`. Little is proved here that is not proved there — the surface exists to test the backbone
against a published account of the subject, and to give a reader of the book a Lean name for
every numbered result in it.

This module imports the section modules that exist and adds nothing of its own; the plan of the
whole library is `plans/NumlibSurface/Brezis/`.

## Naming

A declaration is named for the result it states: `theorem_4_2` is Theorem 4.2, `lemma_4_1` is
Lemma 4.1, `proposition_9_3`, `corollary_9_19`; the chapter-local Remarks and Examples carry the
chapter number, `remark_8_4`, `example_1_2`. Several clauses of one result, or the two directions
of an equivalence, are told apart by a trailing word, the plain id staying on the conjunction or
the main clause. The book's unnumbered "Definition." paragraphs are nodes named by content, each
with an equivalence lemma to the backbone object it stands for. Within the library the
dependencies run forwards in the chapter order: a later chapter uses the earlier restatement
rather than reaching past it.

## Scope

Every Theorem, Proposition, Lemma and Corollary of the main text of chapters 1–11 is planned as a
node; numbered Remarks and Examples are nodes when they assert a precise statement; numbered
results of the Comments sections are nodes only when provable with today's Mathlib or a bounded
task (Krein–Milman 1.13, Egorov 4.29, general Young 4.33, the polarization characterization
5.12). Exercises and Problems are not nodes: the few the main text cites as proof steps become
helper lemmas named for what they say, and the named results among the Problems
(Eberlein–Šmulian, Clarkson's inequalities, Poincaré–Wirtinger) are backbone nodes where the plan
needs them. The book is real throughout; the surface states everything over `ℝ` (§11.4 over
`ℂ`), the backbone over `RCLike 𝕜` wherever the proof allows.

## The outline

* §1.1–1.4, `Chapter01`: Hahn–Banach, analytic and geometric; bidual, annihilators; conjugate
  convex functions — Mathlib, `Numlib/Analysis/Normed/Module/Annihilator`,
  `Numlib/Analysis/Convex/Duality`.
* §2.1–2.7, `Chapter02`: Baire, Banach–Steinhaus, open mapping, closed graph; complemented
  subspaces; unbounded operators, the Banach adjoint, the closed range theorem —
  `Numlib/Analysis/Normed/Module/Complemented`, `…/Operator/Unbounded/*`.
* §3.1–3.7, `Chapter03`: weak and weak-* topologies, reflexivity, separability, uniform convexity,
  Milman–Pettis — `Numlib/Analysis/Normed/Module/{WeakClosed,WeakStarMetrizable,MilmanPettis}`,
  `…/Module/Reflexive/*`.
* §4.1–4.5, `Chapter04`: `L^p` spaces — the convergence theorems, Hölder, Fischer–Riesz,
  reflexivity, duality, separability, convolution and mollifiers, Kolmogorov–Riesz–Fréchet —
  Mathlib, `Numlib/MeasureTheory/Function/LpSpace/*`, `…/Function/{EssSupport,LpInterpolation}`.
* §5.1–5.4, `Chapter05`: Hilbert spaces — projection onto convex sets, Riesz–Fréchet,
  Stampacchia, Lax–Milgram, Hilbert sums — Mathlib,
  `Numlib/Analysis/InnerProductSpace/{ConvexProjection,HilbertSum}`, `Numlib/Variational/*`.
* §6.1–6.4, `Chapter06`: compact operators, Schauder, Riesz–Fredholm, spectral decomposition —
  `Numlib/Analysis/Normed/Operator/{Compact,Riesz}`,
  `Numlib/Analysis/InnerProductSpace/CompactSpectral/*`.
* §7.1–7.4, `Chapter07`: maximal monotone operators, Hille–Yosida —
  `Numlib/Analysis/InnerProductSpace/MaximalMonotone`, `Numlib/Analysis/ODE/HilleYosida`.
* §8.1–8.6, `Chapter08`: Sobolev spaces and boundary value problems in one dimension —
  `Numlib/Analysis/Sobolev/Interval/*`, `Numlib/Variational/EllipticInterval/*`.
* §9.1–9.8, `Chapter09`: Sobolev spaces and elliptic boundary value problems in `N` dimensions —
  `Numlib/Analysis/Sobolev/*`, `Numlib/Analysis/PDE/Elliptic/*`.
* §10.1–10.3, `Chapter10`: the heat and wave equations — `Numlib/Analysis/PDE/*`.
* §11.1–11.4, `Chapter11`: finite dimension and codimension, quotients, the sequence spaces
  `ℓ^p`, `c`, `c₀`, complex Banach spaces — `Numlib/Analysis/Normed/Module/{FiniteCodim,Quotient}`,
  `…/Lp/Sequence`, `…/Algebra/Spectrum`.
-/
