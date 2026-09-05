import Numlib.Surface.AtkinsonHan.Ch02.Functionals
import Numlib.Surface.AtkinsonHan.Ch02.GeometricSeries
import Numlib.Surface.AtkinsonHan.Ch02.Operators
import Numlib.Surface.AtkinsonHan.Ch03.BestApprox
import Numlib.Surface.AtkinsonHan.Ch03.InnerProduct
import Numlib.Surface.AtkinsonHan.Ch03.Projections
import Numlib.Surface.AtkinsonHan.Ch03.UniformBounds
import Numlib.Surface.AtkinsonHan.Ch05.Calculus
import Numlib.Surface.AtkinsonHan.Ch05.ConjugateGradient
import Numlib.Surface.AtkinsonHan.Ch05.FixedPoint
import Numlib.Surface.AtkinsonHan.Ch05.LinearIteration
import Numlib.Surface.AtkinsonHan.Ch05.Newton
import Numlib.Surface.AtkinsonHan.Ch08.BilinearForms
import Numlib.Surface.AtkinsonHan.Ch08.Existence
import Numlib.Surface.AtkinsonHan.Ch08.GeneralizedLaxMilgram
import Numlib.Surface.AtkinsonHan.Ch08.LaxMilgram
import Numlib.Surface.AtkinsonHan.Ch09.CG
import Numlib.Surface.AtkinsonHan.Ch09.Galerkin
import Numlib.Surface.AtkinsonHan.Ch09.PetrovGalerkin
import Numlib.Surface.AtkinsonHan.Ch09.Strang

/-!
# Surface library: Atkinson–Han, *Theoretical Numerical Analysis* (3rd ed.)

Covering §2.3–2.5, §3.3–3.7, §5.1–5.4, §5.6, §8.2–8.3, §8.7 and Chapter 9.

Chapter-by-chapter statements faithful to the book, proved by specializing the backbone
(`Numlib`). Plan: `tracker/atkinsonhan-*.md`. Modules are added here as they are written.
-/
