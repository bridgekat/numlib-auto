import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Approximation.BestApprox
import Numlib.Eigen.MinMax
import Numlib.Eigen.Perturbation
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.CG
import Numlib.Krylov.CR
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.Relations
import Numlib.Krylov.Subspace
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearSolve.Perturbation
import Numlib.LinearSolve.Projection.Basic
import Numlib.LinearSolve.Projection.OneDimensional
import Numlib.LinearSolve.Projection.Optimality
import Numlib.LinearSolve.Stationary.Basic
import Numlib.LinearSolve.Stationary.DiagDominant
import Numlib.LinearSolve.Stationary.Splitting
import Numlib.Nonlinear.FixedPoint
import Numlib.Nonlinear.Newton
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import Numlib.Surface.AtkinsonHan
import Numlib.Surface.AtkinsonHan.Chapter02.Section03
import Numlib.Surface.AtkinsonHan.Chapter02.Section04
import Numlib.Surface.AtkinsonHan.Chapter02.Section05
import Numlib.Surface.AtkinsonHan.Chapter03.Section03
import Numlib.Surface.AtkinsonHan.Chapter03.Section04
import Numlib.Surface.AtkinsonHan.Chapter03.Section06
import Numlib.Surface.AtkinsonHan.Chapter03.Section07
import Numlib.Surface.AtkinsonHan.Chapter05.Section01
import Numlib.Surface.AtkinsonHan.Chapter05.Section02
import Numlib.Surface.AtkinsonHan.Chapter05.Section03
import Numlib.Surface.AtkinsonHan.Chapter05.Section04
import Numlib.Surface.AtkinsonHan.Chapter05.Section06
import Numlib.Surface.AtkinsonHan.Chapter08.Section02
import Numlib.Surface.AtkinsonHan.Chapter08.Section03
import Numlib.Surface.AtkinsonHan.Chapter08.Section07
import Numlib.Surface.AtkinsonHan.Chapter09.Section01
import Numlib.Surface.AtkinsonHan.Chapter09.Section02
import Numlib.Surface.AtkinsonHan.Chapter09.Section03
import Numlib.Surface.AtkinsonHan.Chapter09.Section04
import Numlib.Surface.FongSaunders
import Numlib.Surface.FongSaunders.Section1
import Numlib.Surface.FongSaunders.Section2
import Numlib.Surface.FongSaunders.Section3
import Numlib.Surface.FongSaunders.Section4
import Numlib.Surface.FongSaunders.Section5
import Numlib.Surface.SaadSparse
import Numlib.Surface.SaadSparse.Chapter01.Section11
import Numlib.Surface.SaadSparse.Chapter01.Section12
import Numlib.Surface.SaadSparse.Chapter01.Section13
import Numlib.Surface.SaadSparse.Chapter04.Section01
import Numlib.Surface.SaadSparse.Chapter04.Section02
import Numlib.Surface.SaadSparse.Chapter05.Section01
import Numlib.Surface.SaadSparse.Chapter05.Section03
import Numlib.Surface.SaadSparse.Chapter05.Section04
import Numlib.Surface.SaadSparse.Chapter06.Common
import Numlib.Surface.SaadSparse.Chapter06.Section02
import Numlib.Surface.SaadSparse.Chapter06.Section03
import Numlib.Surface.SaadSparse.Chapter06.Section04
import Numlib.Surface.SaadSparse.Chapter06.Section05
import Numlib.Surface.SaadSparse.Chapter06.Section06
import Numlib.Surface.SaadSparse.Chapter06.Section07
import Numlib.Surface.SaadSparse.Chapter06.Section08
import Numlib.Surface.SaadSparse.Chapter06.Section09
import Numlib.Surface.SaadSparse.Chapter06.Section10
import Numlib.Surface.SaadSparse.Chapter06.Section11
import Numlib.Surface.SaadSparse.Common
import Numlib.Variational.Forms
import Numlib.Variational.Galerkin
import Numlib.Variational.LaxMilgram

/-!
# Numlib

A formal library of numerical analysis, built in two layers.

Everything outside `Numlib.Surface` is the **backbone**: general mathematics, named for its subject
and stated at the weakest hypotheses that carry the proof. It is meant to be read and used without
reference to any particular text, so a doc comment here names its source in full and never by
number.

`Numlib.Surface` holds the **surfaces**, one directory per textbook, aligned to that text section by
section. A surface proves almost nothing of its own: each declaration instantiates a backbone result
at the book's own hypotheses, so a surface reads as an integration test of the backbone against a
published account of the subject. If a surface result does not specialize something, that is a
demand on the backbone rather than licence to do new mathematics on the surface.

## The backbone

The layer is organized by subject, not by book. `Numlib.Analysis`, `Numlib.LinearAlgebra` and
`Numlib.RingTheory` are Mathlib-shaped material that Mathlib lacks, on paths mirroring where each
would go if contributed. The rest is the subject matter: `Numlib.LinearSolve` for perturbation
theory, stationary iterations and projection methods; `Numlib.Krylov` for the Krylov spine;
`Numlib.Variational` for sesquilinear forms, Lax–Milgram and Galerkin; `Numlib.Nonlinear` for fixed
points and Newton's method; `Numlib.Approximation` and `Numlib.Eigen` for best approximation and the
eigenvalue bounds.

Two conventions run through it. **An iterate is specified by what it optimizes, not by the algorithm
that computes it**, so a theorem about "MINRES" is a theorem about any sequence satisfying the
minimal-residual specification, and MINRES, GMRES, CR and MINRES-QLP all inherit it. And **a
spectral hypothesis is a quadratic-form bound** — `LinearMap.IsSymmetricBoundedBy A lmin lmax`
rather than a list of eigenvalues — which passes to compressions, so the Chebyshev-type bounds are
proved in an arbitrary inner product space with no functional calculus and no finite dimension.

## The surfaces

`Numlib.Surface.SaadSparse` is Y. Saad, *Iterative Methods for Sparse Linear Systems* (SIAM, 2nd
ed., 2003), covering §1.11–1.13, §4.1–4.2 and Chapters 5 and 6. `Numlib.Surface.FongSaunders` is
D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison* (2012), complete.
`Numlib.Surface.AtkinsonHan` is K. Atkinson and W. Han, *Theoretical Numerical Analysis: A
Functional Analysis Framework* (Springer, 3rd ed., 2009), covering §2.3–2.5, §3.3–3.7, §5.1–5.4,
§5.6, §8.2–8.3, §8.7 and Chapter 9. Each book's root module is its index: the section-by-section
outline, the ambient conventions, what is deferred, and the places where formalizing the book
corrected it.

**Surface declarations are named for the results they state**, so the name is the index:
`theorem_6_29` is Saad's Theorem 6.29 and `equation_6_43` is his (6.43). Where one numbered result
needs several declarations — its clauses, its CG and its MINRES form, a strict beside a nonstrict
version — a trailing word distinguishes them, as in `theorem_2_2_a` and `theorem_3_1_minres`. A
book's declarations sit in one flat namespace, and `ChapterNN/SectionNN` is the module for §NN.NN.

## References

* K. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd
  edition, Springer, 2009.
* D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison*, SQU Journal for
  Science 17 (2012) 44–62.
* Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003.
-/
