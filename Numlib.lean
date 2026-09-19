import Numlib.Algebra.LinearRecurrence
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.Calculus.ContDiffOnIcc
import Numlib.Analysis.Calculus.CurvilinearLaplacian
import Numlib.Analysis.Calculus.DerivativeTest
import Numlib.Analysis.Calculus.IteratedFDeriv
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Calculus.PartialDeriv
import Numlib.Analysis.Calculus.RootMultiplicity
import Numlib.Analysis.Calculus.Taylor
import Numlib.Analysis.Complex.Harmonic
import Numlib.Analysis.Convex
import Numlib.Analysis.Convex.Bifunction.Algebra
import Numlib.Analysis.Convex.Bifunction.Cofinite
import Numlib.Analysis.Convex.Caratheodory
import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Concave
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Duality.Barrier
import Numlib.Analysis.Convex.Duality.ConcaveConj
import Numlib.Analysis.Convex.Duality.ConcaveOps
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Duality.FiniteProduct
import Numlib.Analysis.Convex.Duality.Gauge
import Numlib.Analysis.Convex.Duality.GaugeLike
import Numlib.Analysis.Convex.Duality.HomConePolar
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Duality.PolarBounded
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Duality.RelintSeparation
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Duality.SupportRelint
import Numlib.Analysis.Convex.Epigraph
import Numlib.Analysis.Convex.Eponyms
import Numlib.Analysis.Convex.EuclideanProd
import Numlib.Analysis.Convex.Exposed
import Numlib.Analysis.Convex.Extremum.Adjoint
import Numlib.Analysis.Convex.Extremum.ConeDuality
import Numlib.Analysis.Convex.Extremum.Fenchel
import Numlib.Analysis.Convex.Extremum.Lagrangian
import Numlib.Analysis.Convex.Extremum.Maximum
import Numlib.Analysis.Convex.Extremum.Minimum
import Numlib.Analysis.Convex.Extremum.Moreau
import Numlib.Analysis.Convex.Extremum.MoreauGradient
import Numlib.Analysis.Convex.Extremum.Normal
import Numlib.Analysis.Convex.Extremum.Perturbation
import Numlib.Analysis.Convex.Extremum.Program
import Numlib.Analysis.Convex.Extremum.Projection
import Numlib.Analysis.Convex.Extremum.Prox
import Numlib.Analysis.Convex.Face
import Numlib.Analysis.Convex.Gateaux
import Numlib.Analysis.Convex.Helly
import Numlib.Analysis.Convex.HellyRefined
import Numlib.Analysis.Convex.Homogeneous
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.HullDirections
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Lattice
import Numlib.Analysis.Convex.Line
import Numlib.Analysis.Convex.LinearInequalities
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Analysis.Convex.Operations.Epi
import Numlib.Analysis.Convex.Operations.Hull
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Operations.InfConv
import Numlib.Analysis.Convex.Polyhedral.Closedness
import Numlib.Analysis.Convex.Polyhedral.Cone
import Numlib.Analysis.Convex.Polyhedral.Conjugate
import Numlib.Analysis.Convex.Polyhedral.Defs
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Polyhedral.Faces
import Numlib.Analysis.Convex.Polyhedral.Function
import Numlib.Analysis.Convex.Polyhedral.Homogeneous
import Numlib.Analysis.Convex.Polyhedral.NormalForm
import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Polyhedral.Recession
import Numlib.Analysis.Convex.Polyhedral.Separation
import Numlib.Analysis.Convex.Polyhedral.Simplicial
import Numlib.Analysis.Convex.Process.Basic
import Numlib.Analysis.Convex.Process.Duality
import Numlib.Analysis.Convex.Process.Linear
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Recession.Cone
import Numlib.Analysis.Convex.Recession.ConeHull
import Numlib.Analysis.Convex.Recession.Conjugate
import Numlib.Analysis.Convex.Recession.Function
import Numlib.Analysis.Convex.Recession.PiSum
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Convex.Representation
import Numlib.Analysis.Convex.Saddle.Closure
import Numlib.Analysis.Convex.Saddle.Conjugate
import Numlib.Analysis.Convex.Saddle.Continuity
import Numlib.Analysis.Convex.Saddle.Correspondence
import Numlib.Analysis.Convex.Saddle.Defs
import Numlib.Analysis.Convex.Saddle.Differential
import Numlib.Analysis.Convex.Saddle.Equiv
import Numlib.Analysis.Convex.Saddle.Existence
import Numlib.Analysis.Convex.Saddle.Kernel
import Numlib.Analysis.Convex.Saddle.Minimax
import Numlib.Analysis.Convex.Saddle.Monotone
import Numlib.Analysis.Convex.Saddle.Rademacher
import Numlib.Analysis.Convex.Saddle.Real
import Numlib.Analysis.Convex.Saddle.Subdifferential
import Numlib.Analysis.Convex.Separation
import Numlib.Analysis.Convex.Simplicial
import Numlib.Analysis.Convex.StrictConvexSpace
import Numlib.Analysis.Convex.Subdifferential.Approx
import Numlib.Analysis.Convex.Subdifferential.BoundaryDirDeriv
import Numlib.Analysis.Convex.Subdifferential.Bounded
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.Convex.Subdifferential.Cofinite
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.Analysis.Convex.Subdifferential.Differentiability
import Numlib.Analysis.Convex.Subdifferential.EssentiallySmooth
import Numlib.Analysis.Convex.Subdifferential.Existence
import Numlib.Analysis.Convex.Subdifferential.Gradient
import Numlib.Analysis.Convex.Subdifferential.GradientLimit
import Numlib.Analysis.Convex.Subdifferential.Integral
import Numlib.Analysis.Convex.Subdifferential.Legendre
import Numlib.Analysis.Convex.Subdifferential.LegendreType
import Numlib.Analysis.Convex.Subdifferential.Monotone
import Numlib.Analysis.Convex.Subdifferential.OneDim
import Numlib.Analysis.Convex.Subdifferential.Preservation
import Numlib.Analysis.Convex.Subdifferential.Primitive
import Numlib.Analysis.Convex.Subdifferential.Rademacher
import Numlib.Analysis.Convex.Subdifferential.Reconstruction
import Numlib.Analysis.Convex.Subdifferential.StrictlyConvex
import Numlib.Analysis.Convex.Subdifferential.Uniqueness
import Numlib.Analysis.Convex.Tangent
import Numlib.Analysis.Convex.Uniform
import Numlib.Analysis.Convolution.Lp
import Numlib.Analysis.Fourier.CosineBasis
import Numlib.Analysis.Fourier.DFT
import Numlib.Analysis.Fourier.Dirichlet
import Numlib.Analysis.Fourier.FourierIntegral
import Numlib.Analysis.Fourier.LogSingleLayer
import Numlib.Analysis.Fourier.Periodisation
import Numlib.Analysis.Fourier.SineBasis
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Fourier.TrigonometricProduct
import Numlib.Analysis.Fourier.Truncation
import Numlib.Analysis.Fourier.Uncertainty
import Numlib.Analysis.HarmonicPolynomial
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.CompactSpectral
import Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis
import Numlib.Analysis.InnerProductSpace.CompactSpectral.Normal
import Numlib.Analysis.InnerProductSpace.ConvexProjection
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.InnerProductSpace.EuclideanProd
import Numlib.Analysis.InnerProductSpace.GramDeterminant
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.InnerProductSpace.HilbertSum
import Numlib.Analysis.InnerProductSpace.MaximalMonotone
import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Analysis.InnerProductSpace.OrthonormalSeries
import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Analysis.InnerProductSpace.WeakCompactness
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Analysis.Normed.Algebra.Spectrum
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Normed.Lp.Sequence
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.Annihilator.ClosedSum
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Analysis.Normed.Module.Complemented
import Numlib.Analysis.Normed.Module.DualSeparable
import Numlib.Analysis.Normed.Module.FiniteCodim
import Numlib.Analysis.Normed.Module.MilmanPettis
import Numlib.Analysis.Normed.Module.NormEquivalence
import Numlib.Analysis.Normed.Module.Quotient
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.Analysis.Normed.Module.WeakClosed
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Analysis.Normed.Module.WeakStarMetrizable
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.Analysis.Normed.Operator.Compact
import Numlib.Analysis.Normed.Operator.Compact.Banach
import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Normed.Operator.Multilinear
import Numlib.Analysis.Normed.Operator.Riesz
import Numlib.Analysis.Normed.Operator.Scaling
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint
import Numlib.Analysis.Normed.Operator.Unbounded.Basic
import Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange
import Numlib.Analysis.Normed.Operator.Unbounded.Reflexive
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Analysis.ODE.Cauchy
import Numlib.Analysis.ODE.Gronwall
import Numlib.Analysis.ODE.HilleYosida
import Numlib.Analysis.ODE.LinearSystem
import Numlib.Analysis.ODE.PicardLindelof
import Numlib.Analysis.PDE.Bochner
import Numlib.Analysis.PDE.Elliptic.Dirichlet
import Numlib.Analysis.PDE.Elliptic.MaximumPrinciple
import Numlib.Analysis.PDE.Heat.Classical
import Numlib.Analysis.PDE.Transport
import Numlib.Analysis.Sobolev.Calculus
import Numlib.Analysis.Sobolev.Chart
import Numlib.Analysis.Sobolev.Compactness
import Numlib.Analysis.Sobolev.Cutoff
import Numlib.Analysis.Sobolev.Density
import Numlib.Analysis.Sobolev.Domain
import Numlib.Analysis.Sobolev.Embedding
import Numlib.Analysis.Sobolev.EmbeddingDomain
import Numlib.Analysis.Sobolev.Extension
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.Analysis.Sobolev.Interval
import Numlib.Analysis.Sobolev.Interval.Basic
import Numlib.Analysis.Sobolev.Interval.Density
import Numlib.Analysis.Sobolev.Interval.DifferenceQuotient
import Numlib.Analysis.Sobolev.Interval.Dual
import Numlib.Analysis.Sobolev.Interval.Embedding
import Numlib.Analysis.Sobolev.Interval.Extension
import Numlib.Analysis.Sobolev.Interval.Higher
import Numlib.Analysis.Sobolev.Interval.Zero
import Numlib.Analysis.Sobolev.Mollification
import Numlib.Analysis.Sobolev.MultiIndex
import Numlib.Analysis.Sobolev.Periodic
import Numlib.Analysis.Sobolev.Poincare
import Numlib.Analysis.Sobolev.Reflection
import Numlib.Analysis.Sobolev.RemovableSingularity
import Numlib.Analysis.Sobolev.Slobodeckij
import Numlib.Analysis.Sobolev.Space
import Numlib.Analysis.Sobolev.Tempered
import Numlib.Analysis.Sobolev.WeakDeriv
import Numlib.Analysis.Sobolev.Zero
import Numlib.Analysis.SpecialFunctions.Chebyshev
import Numlib.Analysis.SpecialFunctions.ChebyshevIntegral
import Numlib.Analysis.SpecialFunctions.EulerMaclaurin
import Numlib.Analysis.SpecialFunctions.LaplaceTransform
import Numlib.Analysis.SpecialFunctions.Log
import Numlib.Analysis.SpecialFunctions.SineSum
import Numlib.Analysis.SpecialFunctions.Tribonacci
import Numlib.Analysis.Wavelet.ContinuousTransform
import Numlib.Analysis.Wavelet.Daubechies
import Numlib.Analysis.Wavelet.Haar
import Numlib.Analysis.Wavelet.Multiresolution
import Numlib.Analysis.Wavelet.QuadratureMirror
import Numlib.Approximation.BSpline
import Numlib.Approximation.Bezier
import Numlib.Approximation.BrokenPolynomial
import Numlib.Approximation.Chebyshev
import Numlib.Approximation.CompositeQuadrature
import Numlib.Approximation.DiskQuadrature
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.Extrapolation
import Numlib.Approximation.GaussLobatto
import Numlib.Approximation.GradedMesh
import Numlib.Approximation.Hermite
import Numlib.Approximation.Hyperinterpolation
import Numlib.Approximation.Interpolation
import Numlib.Approximation.Jackson
import Numlib.Approximation.LeastSquares
import Numlib.Approximation.MvPolynomial
import Numlib.Approximation.NewtonCotes
import Numlib.Approximation.NewtonForm
import Numlib.Approximation.NodalInterpolation
import Numlib.Approximation.OrthogonalDecomposition
import Numlib.Approximation.OrthogonalPolynomial
import Numlib.Approximation.OrthogonalPolynomial.Classical
import Numlib.Approximation.OrthogonalPolynomial.LegendreBounds
import Numlib.Approximation.PiecewiseLinearL2
import Numlib.Approximation.Quadrature
import Numlib.Approximation.RidgePolynomial
import Numlib.Approximation.SingularIntegral
import Numlib.Approximation.SobolevInterpolation
import Numlib.Approximation.Spline
import Numlib.Approximation.TrapezoidExactness
import Numlib.Approximation.TriangleQuadrature
import Numlib.Approximation.Trigonometric
import Numlib.Approximation.TrigonometricInterpolation
import Numlib.Approximation.Unisolvent
import Numlib.Combinatorics.Relation.StronglyConnected
import Numlib.Combinatorics.SimpleGraph.Coloring
import Numlib.Combinatorics.SimpleGraph.IndepSet
import Numlib.Combinatorics.SimpleGraph.LevelSet
import Numlib.Conditioning.LinearSystem
import Numlib.Conditioning.LinearSystem.Componentwise
import Numlib.Conditioning.Method
import Numlib.Conditioning.Problem
import Numlib.Direct.Refinement
import Numlib.Direct.Substitution
import Numlib.DomainDecomposition.Schur
import Numlib.DomainDecomposition.Schwarz
import Numlib.Eigen.Deflation
import Numlib.Eigen.Jacobi
import Numlib.Eigen.KrylovEigen
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import Numlib.Eigen.NumericalRange
import Numlib.Eigen.Pencil
import Numlib.Eigen.Perturbation
import Numlib.Eigen.PowerMethod
import Numlib.Eigen.QRAlgorithm
import Numlib.Eigen.RayleighRitz
import Numlib.Eigen.ReducedResolvent
import Numlib.Eigen.Sturm
import Numlib.FiniteDifference.BoundaryValue
import Numlib.FiniteDifference.Derivative
import Numlib.FiniteDifference.Hyperbolic
import Numlib.FiniteDifference.LaxEquivalence
import Numlib.FiniteDifference.Parabolic
import Numlib.FiniteDifference.Stencil
import Numlib.FiniteDifference.TwoLevel
import Numlib.FiniteDifference.VonNeumann
import Numlib.FloatingPoint.InnerProduct
import Numlib.FloatingPoint.LU
import Numlib.FloatingPoint.Model
import Numlib.FloatingPoint.Stationary
import Numlib.FloatingPoint.Substitution
import Numlib.FloatingPoint.System
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
import Numlib.LinearAlgebra.Matrix.BlockDiagonal
import Numlib.LinearAlgebra.Matrix.Cauchy
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.Companion
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.EpsilonNorm
import Numlib.LinearAlgebra.Matrix.FaddeevLeVerrier
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.Jordan
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.LU
import Numlib.LinearAlgebra.Matrix.LU.Elimination
import Numlib.LinearAlgebra.Matrix.LU.Pivoting
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Order
import Numlib.LinearAlgebra.Matrix.PerronFrobenius
import Numlib.LinearAlgebra.Matrix.PlaneRotation
import Numlib.LinearAlgebra.Matrix.PosDef
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Matrix.Similar
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.LinearAlgebra.Sparse.Frobenius
import Numlib.LinearAlgebra.Sparse.Pattern
import Numlib.LinearAlgebra.Sparse.Reordering
import Numlib.LinearAlgebra.Subspace
import Numlib.MeasureTheory.Function.EssSupport
import Numlib.MeasureTheory.Function.LpInterpolation
import Numlib.MeasureTheory.Function.LpSpace.Clarkson
import Numlib.MeasureTheory.Function.LpSpace.Convergence
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.MeasureTheory.Function.LpSpace.KolmogorovRiesz
import Numlib.MeasureTheory.Integral.IntervalIntegral
import Numlib.Multigrid.Basic
import Numlib.Multigrid.FullMultigrid
import Numlib.Multigrid.TwoGrid
import Numlib.Nonlinear.Bisection
import Numlib.Nonlinear.CompletelyContinuous
import Numlib.Nonlinear.DifferenceJacobian
import Numlib.Nonlinear.FixedPoint
import Numlib.Nonlinear.Nemytskii
import Numlib.Nonlinear.Newton
import Numlib.Nonlinear.Order
import Numlib.Nonlinear.QuasiNewton
import Numlib.Nonlinear.ScalarNewton
import Numlib.Nonlinear.Secant
import Numlib.ODE.DifferenceEquation
import Numlib.ODE.Gronwall
import Numlib.ODE.Multistep
import Numlib.ODE.OneStep
import Numlib.ODE.RungeKutta
import Numlib.Optimization.ConjugateGradient
import Numlib.Optimization.Constrained
import Numlib.Optimization.Descent
import Numlib.Optimization.LineSearch
import Numlib.Optimization.QuasiNewton
import Numlib.Order.EReal
import Numlib.Order.GaloisConnection
import Numlib.Preconditioner.ApproximateInverse
import Numlib.Preconditioner.Chebyshev
import Numlib.Preconditioner.ILU
import Numlib.Preconditioner.Polynomial
import Numlib.Probability.MonteCarlo
import Numlib.Projection.Additive
import Numlib.Projection.Basic
import Numlib.Projection.ConjugateDirection
import Numlib.Projection.Coordinate
import Numlib.Projection.OneDimensional
import Numlib.Projection.Optimality
import Numlib.RingTheory.MvPolynomial.TotalDegree
import Numlib.RingTheory.Polynomial.ChebyshevEllipse
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import Numlib.RingTheory.Polynomial.Horner
import Numlib.RingTheory.Polynomial.KernelPolynomial
import Numlib.RingTheory.Polynomial.RuleOfSigns
import Numlib.RingTheory.Polynomial.SchurCohn
import Numlib.Stationary.ADI
import Numlib.Stationary.Basic
import Numlib.Stationary.Block
import Numlib.Stationary.ConsistentlyOrdered
import Numlib.Stationary.DiagDominant
import Numlib.Stationary.RegularSplitting
import Numlib.Stationary.Richardson
import Numlib.Stationary.SPD
import Numlib.Stationary.Splitting
import Numlib.Stationary.Sweep
import Numlib.Topology.Algebra.Polynomial
import Numlib.Topology.ContinuousMap.ArzelaAscoli
import Numlib.Topology.Order.IntermediateValue
import Numlib.Variational.AdvectionDiffusion
import Numlib.Variational.EllipticInterval
import Numlib.Variational.EllipticInterval.BoundaryConditions
import Numlib.Variational.EllipticInterval.MaximumPrinciple
import Numlib.Variational.EllipticInterval.SturmLiouville
import Numlib.Variational.EnergyPairing
import Numlib.Variational.Evolution
import Numlib.Variational.FiniteElementInterval
import Numlib.Variational.Forms
import Numlib.Variational.Galerkin
import Numlib.Variational.Inequality.Approximation
import Numlib.Variational.Inequality.Basic
import Numlib.Variational.Inequality.NormalCone
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

The layer is organized by subject, not by book. The **foundations** are Mathlib-shaped material
that Mathlib lacks, on the paths where each would go if contributed: `Numlib.Analysis` (with the
general convex analysis `Numlib.Analysis.Convex`, at four levels of generality from a bare real
vector space to Euclidean space, and the Sobolev, Fourier and wavelet material),
`Numlib.LinearAlgebra`, `Numlib.RingTheory`, `Numlib.Topology`, `Numlib.Order`, `Numlib.Algebra`,
`Numlib.Combinatorics` and `Numlib.Geometry`. The **subjects** stand on them: `Numlib.Conditioning`
for well-posedness, condition numbers, the consistency–stability–convergence vocabulary and the
perturbation theory of linear systems; `Numlib.FloatingPoint` for the relational rounding model
and the number systems that instantiate it; then the solvers for `A x = b` in their import order —
`Numlib.Direct`, `Numlib.Stationary` and `Numlib.Projection` (the specifications every Krylov
method instantiates), `Numlib.Krylov` for the Krylov spine, and above it `Numlib.Preconditioner`,
`Numlib.Multigrid` and `Numlib.DomainDecomposition`; `Numlib.Eigen` for eigenvalue bounds and
algorithms; `Numlib.Nonlinear` for fixed points, rootfinding and Newton's method;
`Numlib.Optimization` for descent, line-search, quasi-Newton and constrained methods with the
smooth first- and second-order theory; `Numlib.Approximation` for interpolation, quadrature and
best approximation; `Numlib.Variational` for sesquilinear forms, Lax–Milgram, Galerkin and
variational inequalities; `Numlib.ODE` for one-step, multistep and Runge–Kutta methods;
`Numlib.FiniteDifference` for difference schemes and their stability; `Numlib.IntegralEquations`;
and `Numlib.Probability` for what Monte Carlo integration needs.

One boundary is worth stating. The *theory* of an extremum problem — optimality conditions,
duality, existence for convex data — is `Numlib.Analysis.Convex.Extremum`, which sits in the
middle of the convex library's import graph; iterative *methods* and the smooth nonconvex
optimality theory are `Numlib.Optimization`. The dictionary between the two vocabularies
(variational inequalities as normal-cone conditions, best approximation as a proximal map, saddle
points) is where the older numerical modules and the convex library meet.

Two conventions run through it. **An iterate is specified by what it optimizes, not by the algorithm
that computes it**, so a theorem about "MINRES" is a theorem about any sequence satisfying the
minimal-residual specification, and MINRES, GMRES, CR and MINRES-QLP all inherit it. And **a
spectral hypothesis is a quadratic-form bound** — `LinearMap.IsSymmetricBoundedBy A lmin lmax`
rather than a list of eigenvalues — which passes to compressions, so the Chebyshev-type bounds are
proved in an arbitrary inner product space with no functional calculus and no finite dimension.

## What stands on it

The four surfaces of `NumlibSurface` — Saad's *Iterative Methods for Sparse Linear Systems*, Fong
and Saunders' *CG versus MINRES*, Atkinson and Han's *Theoretical Numerical Analysis*, and
Rockafellar's *Convex Analysis* — are that library's index, and each names its own sources. What a
backbone module cites, it cites in full, in its own references section.
-/
