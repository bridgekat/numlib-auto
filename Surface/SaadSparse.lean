import SaadSparse.Basic
import SaadSparse.Ch01.LinearSystems
import SaadSparse.Ch01.PositiveDefinite
import SaadSparse.Ch01.Projectors
import SaadSparse.Ch04.Convergence
import SaadSparse.Ch04.DiagDominant
import SaadSparse.Ch04.SPD
import SaadSparse.Ch04.Splittings
import SaadSparse.Ch05.Additive
import SaadSparse.Ch05.OneDimensional
import SaadSparse.Ch05.Projection
import SaadSparse.Ch06.Arnoldi
import SaadSparse.Ch06.Basic
import SaadSparse.Ch06.CG
import SaadSparse.Ch06.CR
import SaadSparse.Ch06.Chebyshev
import SaadSparse.Ch06.Convergence
import SaadSparse.Ch06.DQGMRES
import SaadSparse.Ch06.FOM
import SaadSparse.Ch06.FaberManteuffel
import SaadSparse.Ch06.GCR
import SaadSparse.Ch06.GMRES
import SaadSparse.Ch06.Givens
import SaadSparse.Ch06.Lanczos
import SaadSparse.Ch06.Relations
import SaadSparse.Ch06.Residual
import SaadSparse.Ch06.Smoothing

/-!
# Surface library: Saad, *Iterative Methods for Sparse Linear Systems* (2nd ed.)

Covering §1.11–§1.13, §4.1–§4.2, Ch. 5 and Ch. 6.

Chapter-by-chapter statements faithful to the book, proved by specializing the backbone
(`Numlib`). Plan: `plans/surface/SaadSparse*.md`. Modules are added here as they are written.
-/
