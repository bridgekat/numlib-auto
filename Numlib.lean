import Numlib.Analysis.Calculus.CurvilinearLaplacian
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Complex.Harmonic
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Gateaux
import Numlib.Analysis.Convex.SaddlePoint
import Numlib.Analysis.Convex.StrictConvexSpace
import Numlib.Analysis.Convex.Uniform
import Numlib.Analysis.Fourier.CosineBasis
import Numlib.Analysis.Fourier.DFT
import Numlib.Analysis.Fourier.Dirichlet
import Numlib.Analysis.Fourier.LogSingleLayer
import Numlib.Analysis.Fourier.Periodisation
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Fourier.TrigonometricProduct
import Numlib.Analysis.Fourier.Truncation
import Numlib.Analysis.HarmonicPolynomial
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.CompactSpectral
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.InnerProductSpace.OrthonormalSeries
import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Analysis.InnerProductSpace.WeakCompactness
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.Analysis.Normed.Module.NormEquivalence
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.Analysis.Normed.Operator.Compact
import Numlib.Analysis.Normed.Operator.Riesz
import Numlib.Analysis.Normed.Operator.Scaling
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Analysis.ODE.PicardLindelof
import Numlib.Analysis.Sobolev.Domain
import Numlib.Analysis.Sobolev.Periodic
import Numlib.Analysis.Sobolev.Space
import Numlib.Analysis.Sobolev.WeakDeriv
import Numlib.Analysis.SpecialFunctions.Chebyshev
import Numlib.Analysis.SpecialFunctions.ChebyshevIntegral
import Numlib.Analysis.Wavelet.Daubechies
import Numlib.Analysis.Wavelet.Haar
import Numlib.Analysis.Wavelet.Multiresolution
import Numlib.Analysis.Wavelet.QuadratureMirror
import Numlib.Approximation.BestApprox
import Numlib.Approximation.Chebyshev
import Numlib.Approximation.CompositeQuadrature
import Numlib.Approximation.DiskQuadrature
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.GradedMesh
import Numlib.Approximation.Hermite
import Numlib.Approximation.Hyperinterpolation
import Numlib.Approximation.Interpolation
import Numlib.Approximation.Jackson
import Numlib.Approximation.LeastSquares
import Numlib.Approximation.MvPolynomial
import Numlib.Approximation.NodalInterpolation
import Numlib.Approximation.OrthogonalDecomposition
import Numlib.Approximation.OrthogonalPolynomial
import Numlib.Approximation.PiecewiseLinearL2
import Numlib.Approximation.Quadrature
import Numlib.Approximation.RidgePolynomial
import Numlib.Approximation.TrapezoidExactness
import Numlib.Approximation.Trigonometric
import Numlib.Approximation.TrigonometricInterpolation
import Numlib.Approximation.Unisolvent
import Numlib.Combinatorics.Relation.StronglyConnected
import Numlib.Combinatorics.SimpleGraph.Coloring
import Numlib.Combinatorics.SimpleGraph.IndepSet
import Numlib.Combinatorics.SimpleGraph.LevelSet
import Numlib.Eigen.Deflation
import Numlib.Eigen.Jacobi
import Numlib.Eigen.KrylovEigen
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import Numlib.Eigen.NumericalRange
import Numlib.Eigen.Perturbation
import Numlib.Eigen.PowerMethod
import Numlib.Eigen.QRAlgorithm
import Numlib.Eigen.RayleighRitz
import Numlib.Eigen.ReducedResolvent
import Numlib.FiniteDifference.LaxEquivalence
import Numlib.FiniteDifference.TwoLevel
import Numlib.FloatingPoint.InnerProduct
import Numlib.FloatingPoint.Model
import Numlib.FloatingPoint.Stationary
import Numlib.Geometry.Euclidean.TriangleShape
import Numlib.IntegralEquations.Basic
import Numlib.IntegralEquations.L2Kernel
import Numlib.IntegralEquations.Nystrom
import Numlib.IntegralEquations.ProductIntegration
import Numlib.IntegralEquations.SecondKind
import Numlib.IntegralEquations.WeaklySingular
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.BiLanczos
import Numlib.Krylov.Block
import Numlib.Krylov.CG
import Numlib.Krylov.CGW
import Numlib.Krylov.CR
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Convergence.MinRes
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Convergence.Superlinear
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.NormalEquations
import Numlib.Krylov.OrthogonalPolynomials
import Numlib.Krylov.Perturbed
import Numlib.Krylov.Preconditioned
import Numlib.Krylov.QuasiMinRes
import Numlib.Krylov.Relations
import Numlib.Krylov.Singular
import Numlib.Krylov.Subspace
import Numlib.Krylov.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.Assembly
import Numlib.LinearAlgebra.Matrix.Cauchy
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.EpsilonNorm
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearAlgebra.Matrix.Order
import Numlib.LinearAlgebra.Matrix.PerronFrobenius
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.LinearAlgebra.Sparse.Frobenius
import Numlib.LinearAlgebra.Sparse.Pattern
import Numlib.LinearAlgebra.Sparse.Reordering
import Numlib.LinearSolve.DomainDecomposition.Schur
import Numlib.LinearSolve.DomainDecomposition.Schwarz
import Numlib.LinearSolve.Multigrid.Basic
import Numlib.LinearSolve.Multigrid.FullMultigrid
import Numlib.LinearSolve.Multigrid.TwoGrid
import Numlib.LinearSolve.Perturbation
import Numlib.LinearSolve.Preconditioner.ApproximateInverse
import Numlib.LinearSolve.Preconditioner.Chebyshev
import Numlib.LinearSolve.Preconditioner.ILU
import Numlib.LinearSolve.Preconditioner.Polynomial
import Numlib.LinearSolve.Projection.Additive
import Numlib.LinearSolve.Projection.Basic
import Numlib.LinearSolve.Projection.Coordinate
import Numlib.LinearSolve.Projection.OneDimensional
import Numlib.LinearSolve.Projection.Optimality
import Numlib.LinearSolve.Stationary.ADI
import Numlib.LinearSolve.Stationary.Basic
import Numlib.LinearSolve.Stationary.Block
import Numlib.LinearSolve.Stationary.ConsistentlyOrdered
import Numlib.LinearSolve.Stationary.DiagDominant
import Numlib.LinearSolve.Stationary.RegularSplitting
import Numlib.LinearSolve.Stationary.SPD
import Numlib.LinearSolve.Stationary.Splitting
import Numlib.Nonlinear.CompletelyContinuous
import Numlib.Nonlinear.FixedPoint
import Numlib.Nonlinear.Newton
import Numlib.RingTheory.MvPolynomial.TotalDegree
import Numlib.RingTheory.Polynomial.ChebyshevEllipse
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import Numlib.RingTheory.Polynomial.KernelPolynomial
import Numlib.Topology.ContinuousMap.ArzelaAscoli
import Numlib.Variational.AubinNitsche
import Numlib.Variational.Forms
import Numlib.Variational.Galerkin
import Numlib.Variational.Inequality.Approximation
import Numlib.Variational.Inequality.Basic
import Numlib.Variational.LaxMilgram
import Numlib.Variational.Minimization
import Numlib.Variational.ProjectionMethod
import Numlib.Variational.WeakMinimization

/-!
# Numlib

The **backbone** of a formal library of numerical analysis: general mathematics, named for its
subject and stated at the weakest hypotheses that carry the proof. It is meant to be read and used
without reference to any particular text, so a doc comment here names its source in full and never
by number.

The other layer is the sibling library `NumlibSurface`, one directory per textbook, aligned to that
text section by section. A surface proves almost nothing of its own: each declaration instantiates a
backbone result at the book's own hypotheses, so a surface reads as an integration test of this
library against a published account of the subject. If a surface result does not specialize
something, that is a demand on the backbone rather than licence to do new mathematics there.

The two are separate Lake libraries so that the dependency cannot run the wrong way: `Numlib`
imports no surface, and nothing here may be justified by a book's own numbering.

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

## What stands on it

The three surfaces of `NumlibSurface` — Saad's *Iterative Methods for Sparse Linear Systems*, Fong
and Saunders' *CG versus MINRES*, and Atkinson and Han's *Theoretical Numerical Analysis* — are that
library's index, and each names its own sources. What a backbone module cites, it cites in full, in
its own references section.
-/
