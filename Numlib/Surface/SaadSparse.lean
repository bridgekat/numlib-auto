import Numlib.Surface.SaadSparse.Basic
import Numlib.Surface.SaadSparse.Ch01.LinearSystems
import Numlib.Surface.SaadSparse.Ch01.PositiveDefinite
import Numlib.Surface.SaadSparse.Ch01.Projectors
import Numlib.Surface.SaadSparse.Ch04.Convergence
import Numlib.Surface.SaadSparse.Ch04.DiagDominant
import Numlib.Surface.SaadSparse.Ch04.SPD
import Numlib.Surface.SaadSparse.Ch04.Splittings
import Numlib.Surface.SaadSparse.Ch05.Additive
import Numlib.Surface.SaadSparse.Ch05.OneDimensional
import Numlib.Surface.SaadSparse.Ch05.Projection
import Numlib.Surface.SaadSparse.Ch06.Arnoldi
import Numlib.Surface.SaadSparse.Ch06.Basic
import Numlib.Surface.SaadSparse.Ch06.CG
import Numlib.Surface.SaadSparse.Ch06.CR
import Numlib.Surface.SaadSparse.Ch06.Chebyshev
import Numlib.Surface.SaadSparse.Ch06.Convergence
import Numlib.Surface.SaadSparse.Ch06.DQGMRES
import Numlib.Surface.SaadSparse.Ch06.FOM
import Numlib.Surface.SaadSparse.Ch06.FaberManteuffel
import Numlib.Surface.SaadSparse.Ch06.GCR
import Numlib.Surface.SaadSparse.Ch06.GMRES
import Numlib.Surface.SaadSparse.Ch06.Givens
import Numlib.Surface.SaadSparse.Ch06.Lanczos
import Numlib.Surface.SaadSparse.Ch06.Relations
import Numlib.Surface.SaadSparse.Ch06.Residual
import Numlib.Surface.SaadSparse.Ch06.Smoothing

/-!
# Surface library: Saad, *Iterative Methods for Sparse Linear Systems* (2nd ed.)

Covering §1.11–§1.13, §4.1–§4.2, Ch. 5 and Ch. 6.

Chapter-by-chapter statements faithful to the book, proved by specializing the backbone
(`Numlib`). Plan: `tracker/saadsparse-*.md`. Modules are added here as they are written.
-/
