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
import Numlib.Variational.Forms
import Numlib.Variational.Galerkin
import Numlib.Variational.LaxMilgram

/-!
# The backbone

Every module of the general layer, so that a surface library can depend on the backbone as a whole
without depending on the surface. `Numlib` itself imports this together with the surface roots.
-/
