import Numlib.Optimization.MeasureDomination
import Numlib.Optimization.RegularizedTaylorModel
import Numlib.Optimization.SecularResolvent
import Numlib.Optimization.TaylorCriticality
import NumlibSurface.CartisGouldToint.AppendixA.Section01
import NumlibSurface.CartisGouldToint.AppendixA.Section02
import NumlibSurface.CartisGouldToint.AppendixA.Section03
import NumlibSurface.CartisGouldToint.AppendixA.Section04
import NumlibSurface.CartisGouldToint.AppendixA.Section05
import NumlibSurface.CartisGouldToint.AppendixA.Section06
import NumlibSurface.CartisGouldToint.AppendixA.Section07
import NumlibSurface.CartisGouldToint.AppendixA.Section08
import NumlibSurface.CartisGouldToint.AppendixA.Section08.FractionalFactorial
import NumlibSurface.CartisGouldToint.AppendixA.Section09
import NumlibSurface.CartisGouldToint.AppendixA.Section10
import NumlibSurface.CartisGouldToint.AppendixB.Chapter02
import NumlibSurface.CartisGouldToint.AppendixB.Chapter02.FiniteValley
import NumlibSurface.CartisGouldToint.AppendixB.Chapter02.FiniteValleySmooth
import NumlibSurface.CartisGouldToint.AppendixB.Chapter02.Hermite
import NumlibSurface.CartisGouldToint.AppendixB.Chapter02.Profiles
import NumlibSurface.CartisGouldToint.AppendixB.Chapter03
import NumlibSurface.CartisGouldToint.AppendixB.Chapter04
import NumlibSurface.CartisGouldToint.AppendixB.Chapter05
import NumlibSurface.CartisGouldToint.AppendixB.Chapter07
import NumlibSurface.CartisGouldToint.AppendixB.Chapter08.TransformedNewton
import NumlibSurface.CartisGouldToint.AppendixB.Chapter09
import NumlibSurface.CartisGouldToint.AppendixB.Chapter10
import NumlibSurface.CartisGouldToint.AppendixB.Chapter12
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import NumlibSurface.CartisGouldToint.Chapter01.Section01.KKTEquality
import NumlibSurface.CartisGouldToint.Chapter01.Section01.KKTInequality
import NumlibSurface.CartisGouldToint.Chapter01.Section01.OptimalityMeasures
import NumlibSurface.CartisGouldToint.Chapter01.Section01.TangentSufficiency
import NumlibSurface.CartisGouldToint.Chapter01.Section02
import NumlibSurface.CartisGouldToint.Chapter01.Section03
import NumlibSurface.CartisGouldToint.Chapter01.Section04
import NumlibSurface.CartisGouldToint.Chapter02.Section01
import NumlibSurface.CartisGouldToint.Chapter02.Section02
import NumlibSurface.CartisGouldToint.Chapter02.Section03
import NumlibSurface.CartisGouldToint.Chapter02.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section01
import NumlibSurface.CartisGouldToint.Chapter03.Section02
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import NumlibSurface.CartisGouldToint.Chapter03.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section05
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import NumlibSurface.CartisGouldToint.Chapter04.Section01.Complexity
import NumlibSurface.CartisGouldToint.Chapter04.Section01.Sharpness
import NumlibSurface.CartisGouldToint.Chapter04.Section02
import NumlibSurface.CartisGouldToint.Chapter05.Section01
import NumlibSurface.CartisGouldToint.Chapter05.Section01.Complexity
import NumlibSurface.CartisGouldToint.Chapter05.Section02
import NumlibSurface.CartisGouldToint.Chapter05.Section03
import NumlibSurface.CartisGouldToint.Chapter05.Section03.FullRankResidual
import NumlibSurface.CartisGouldToint.Chapter05.Section04
import NumlibSurface.CartisGouldToint.Chapter05.Section04.Counterexample
import NumlibSurface.CartisGouldToint.Chapter05.Section04.PhaseComplexity
import NumlibSurface.CartisGouldToint.Chapter05.Section05
import NumlibSurface.CartisGouldToint.Chapter05.Section05.Bounds
import NumlibSurface.CartisGouldToint.Chapter05.Section05.Complexity
import NumlibSurface.CartisGouldToint.Chapter05.Section05.Decrease
import NumlibSurface.CartisGouldToint.Chapter06.Section01
import NumlibSurface.CartisGouldToint.Chapter06.Section02
import NumlibSurface.CartisGouldToint.Chapter06.Section02.HigherOrder
import NumlibSurface.CartisGouldToint.Chapter06.Section03
import NumlibSurface.CartisGouldToint.Chapter07.Section01
import NumlibSurface.CartisGouldToint.Chapter07.Section02.BoundedBoundary
import NumlibSurface.CartisGouldToint.Chapter07.Section02.Execution
import NumlibSurface.CartisGouldToint.Chapter07.Section02.PenaltyMethods
import NumlibSurface.CartisGouldToint.Chapter07.Section02.Targets
import NumlibSurface.CartisGouldToint.Chapter08.Section01
import NumlibSurface.CartisGouldToint.Chapter08.Section02
import NumlibSurface.CartisGouldToint.Chapter08.Section03
import NumlibSurface.CartisGouldToint.Chapter09.Section01
import NumlibSurface.CartisGouldToint.Chapter09.Section02
import NumlibSurface.CartisGouldToint.Chapter09.Section03
import NumlibSurface.CartisGouldToint.Chapter09.Section03.EarlyTermination
import NumlibSurface.CartisGouldToint.Chapter09.Section03.HardCase
import NumlibSurface.CartisGouldToint.Chapter09.Section03.HardCaseBounds
import NumlibSurface.CartisGouldToint.Chapter09.Section04
import NumlibSurface.CartisGouldToint.Chapter10.Section01
import NumlibSurface.CartisGouldToint.Chapter10.Section01.LanczosIdentities
import NumlibSurface.CartisGouldToint.Chapter10.Section02
import NumlibSurface.CartisGouldToint.Chapter10.Section02.Algorithms
import NumlibSurface.CartisGouldToint.Chapter10.Section02.Monotonicity
import NumlibSurface.CartisGouldToint.Chapter10.Section02.ResidualIdentity
import NumlibSurface.CartisGouldToint.Chapter10.Section02.Stopping
import NumlibSurface.CartisGouldToint.Chapter10.Section03
import NumlibSurface.CartisGouldToint.Chapter10.Section03.Monotonicity
import NumlibSurface.CartisGouldToint.Chapter10.Section03.Stopping
import NumlibSurface.CartisGouldToint.Chapter11.Section01
import NumlibSurface.CartisGouldToint.Chapter11.Section01.SignedClassification
import NumlibSurface.CartisGouldToint.Chapter11.Section01.SignedDefinite
import NumlibSurface.CartisGouldToint.Chapter11.Section01.SignedDiagonal
import NumlibSurface.CartisGouldToint.Chapter11.Section01.SignedRegularization
import NumlibSurface.CartisGouldToint.Chapter11.Section02
import NumlibSurface.CartisGouldToint.Chapter11.Section02.RadiusWeightLimits
import NumlibSurface.CartisGouldToint.Chapter11.Section02.SecularLimits
import NumlibSurface.CartisGouldToint.Chapter11.Section03
import NumlibSurface.CartisGouldToint.Chapter12.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section01.Curves
import NumlibSurface.CartisGouldToint.Chapter12.Section01.TaylorCriteria
import NumlibSurface.CartisGouldToint.Chapter12.Section02
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqp
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpBounds
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpComplexity
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpGeneralSharpness
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpInner
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpInnerTermination
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpSharpness
import NumlibSurface.CartisGouldToint.Chapter12.Section02.EqualityCounterexample
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ModelBounds
import NumlibSurface.CartisGouldToint.Chapter12.Section02.Sharpness
import NumlibSurface.CartisGouldToint.Chapter12.Section02.TRq
import NumlibSurface.CartisGouldToint.Chapter12.Section03
import NumlibSurface.CartisGouldToint.Chapter13.Section01
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDA
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDACounterexample
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDACubicStop
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDAJets
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDARadii
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDAShortCounterexample
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDAUniformAccuracy
import NumlibSurface.CartisGouldToint.Chapter13.Section01.TRqIDA
import NumlibSurface.CartisGouldToint.Chapter13.Section02
import NumlibSurface.CartisGouldToint.Chapter13.Section03
import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDA
import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDACounterexample
import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDACubicStop
import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDAShortCounterexample
import NumlibSurface.CartisGouldToint.Chapter14.Section01
import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpC
import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpCBounds
import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpCInnerDecrease
import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpCInnerExistence
import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpCSharpness
import NumlibSurface.CartisGouldToint.Chapter14.Section01.Counterexamples
import NumlibSurface.CartisGouldToint.Chapter14.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section02.SparseBox
import NumlibSurface.CartisGouldToint.Chapter14.Section03
import NumlibSurface.CartisGouldToint.Chapter14.Section03.BoundaryCounterexample
import NumlibSurface.CartisGouldToint.Chapter14.Section03.BoundaryRegularization
import NumlibSurface.CartisGouldToint.Chapter14.Section03.Curves
import NumlibSurface.CartisGouldToint.Chapter14.Section03.ResidualJets
import NumlibSurface.CartisGouldToint.Chapter14.Section03.Sufficiency
import NumlibSurface.CartisGouldToint.Chapter14.Section03.TwoPhase
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDADecrease
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDAComplexity
import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDAUniformAccuracy
import NumlibSurface.CartisGouldToint.Chapter14.Section02.ModelBounds
import NumlibSurface.CartisGouldToint.Chapter14.Section03.CostCrossover
import NumlibSurface.CartisGouldToint.Chapter14.Section03.PhaseOneComplexity
import NumlibSurface.CartisGouldToint.Chapter13.Section03.TransverseObjective
import NumlibSurface.CartisGouldToint.Chapter14.Section02.TRDecreaseData
import NumlibSurface.CartisGouldToint.Chapter14.Section02.TRDecreaseCounterexample
import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDACertificationCounterexample
import NumlibSurface.CartisGouldToint.Chapter14.Section02.ARqpEDAUniv

/-!
# Cartis, Gould and Toint: Evaluation Complexity of Algorithms for Nonconvex Optimization

Surface formalization of Coralia Cartis, Nicholas I. M. Gould and Philippe L. Toint,
*Evaluation Complexity of Algorithms for Nonconvex Optimization: Theory, Computation, and
Perspectives*, SIAM, 2022. Source: the supplied OCR Markdown under
`references/evaluation-complexity-of-algorithms-for-nonconvex-optimization/`.

## Scope and current implementation

The plans inventory all 14 chapters and both appendices, including all 266 explicitly labeled
theorems, lemmas, corollaries and algorithms in the transcription. A plan node records an intended
declaration, not an established theorem. The implemented surface covers unconstrained local
optimality through order three, necessary convex-constrained local conditions, first-order
objective assumptions, the actual SDBA iteration and corrected oracle bounds, exact-line-search
iteration complexity and sharpness with global ray minima, quadratic Cauchy
decrease, lawful TR1 and AR1 traces and their complete first-order evaluation bounds and sharpness,
Newton derivative-evaluation sharpness, full TR2 first- and second-order complexity and
sharpness with actual Hessians, all Taylor
remainder theorems in Appendix A.8, uniform finite Hermite interpolation in Appendix A.9,
first- and second-order cubic-regularization complexity and sharpness with actual model minimizers,
general-metric quadratic-subproblem optimality, secular root and Taylor bounds, transformed
resolvent convexity and supporting-line bounds, actual metric resolvent derivatives of all orders,
the exact factorization-based secular derivative algorithm, source conventions for sequences
and induced norms, ordinary and generalized spectral endpoints with eigenvalue perturbation
bounds, first- and joint second-order regularized trust-region complexity, complete inexact
regularized Newton complexity with actual projected-curvature tests,
inexact Newton method-class estimates,
the full higher-order regularization algorithm, step and decrease bounds, first- and second-order
termination, and first- to third-order finite iterate-quality complexity and sharpness,
symmetric tensor
diagonal/operator norm equality and maxima, the finite-series estimates of Appendix A.10, and
the square-root scaling bound of Appendix B.3, constrained criticality measures through order
three, Taylor-gap stability and a corrected uniform-growth sufficient condition, and nonsmooth
composite Taylor models with their value bounds and first-model optimality, measure-dominated
convergence rates with actual iteration and oracle counts, curve-based linesearch obstruction,
Taylor optimality criteria through cubic order and radius cascading, and genuine inexact Taylor
jet error and model-decrease estimates, arbitrary-order curve necessary conditions,
matching TRq evaluation upper and lower bounds, actual ARqp outer transitions, arbitrary-choice
finite inner progress and returned-step correctness, full ARqp lower-bound constructions,
true-gap-conditioned ARqp decrease and cached evaluation budgets, and full high-order model
regularity and decrease bounds, constructive quadratic hard-case
minimizer families, and actual preconditioned Lanczos subspace reductions.

General proofs live in the subject-organized backbone: finite descent budgets, multiplicative
parameter counting and invariants, canonical scalar/vector Taylor models, compact-set optimality
gaps and perturbation bounds, feasible linearized gaps, uniform Taylor growth and stability,
nonsmooth composite Taylor models, local-smoothness Taylor gap limits, approximate finite jets,
measure-dominated scalar descent with superlinear and polynomial rates, arbitrary-order
curve expansions, sharp arbitrary-order radial derivatives, complete quadratic kernel
parametrizations, exact Lanczos residuals and raw-recurrence basis identification, and
 linear tolerance counts and exact
finite termination for sublinear explicit power recurrences, full quadratic-model optimality
characterizations, finite-smoothness higher-derivative symmetry and sharp Hölder Taylor bounds,
and actual shifted-operator secular functions with all-order derivatives, Taylor
bounds and unique-root criteria. The surface specializes these to the
book's Euclidean spaces, gradients, tolerances and algorithm parameters.

Subsequent work should use `lake build` followed by `lake exe tracker ready` and `tracker show`.
Complete modules in dependency order, and keep the numbered source correspondence. The
remaining Newton method-class lower bounds, remaining secular theory, constrained guarantees,
inexact-oracle results, the availability coupling for a corrected inner-generated ARqp
complexity theorem, and nonlinear-rate estimates are open.
No claim of whole-book formalization is made by this module.

## Source fidelity


The equality- and inequality-constrained optimality theorems1.1.3/1.1.4 include all
first- and second-order necessary/sufficient clauses under explicit LICQ for necessity;
strict sufficiency uses no constraint qualification. The corrected Theorem1.1.2 uses the
actual tangent critical cone. Section6.2 has both actual constrained regularization
algorithms, all active orders in the decrease and complexity bounds6.2.2/3, and first-order
stopping and cached evaluation counts6.2.5. The original6.2.1 unrestricted-direction clauses
remain wrong; valid bounded-direction clauses have separate names. Section6.3 has the actual
constrained residual algorithm and its normalized first-order stopping/evaluation bound.
The first-attainment theorems use explicit availability of actual legal finite prefixes.

Section7.1 has the actual feasible set, differentiable Lagrangian, minimizer sufficiency and
scaled approximate KKT definition. Section7.2 has the Euclidean target residual, minimal
smoothness assumptions, uniform targetwise derivative/regularization bounds7.2.5, and actual
quadratic penalty, augmented-Lagrangian and shifted barrier identities. The componentwise
alternative sufficient-condition proof remains open separately. The two-phase execution and
its remaining complexity proof are incomplete; their recorded source problems remain.

Section5.1 includes actual residual-power ARpLE definitions, all three normalized derivative
orders, all six exponent choices and Theorem5.1.7's exact finite iterate-quality budget for
actual execution prefixes. Third-order quality permits an empty direction set and is not
genuine algorithm stopping. Section5.5 has the finite-product real factorial, actual Holder
smoothness and universal algorithm, and decrease/derivative lemmas5.5.1/2. Its remaining
parameter and complexity lemmas5.5.3--7 are open. Every universal trial's activated derivative
queries are counted, including rejected and terminal trials.

Weighted regularized/trust-region Lanczos residual bounds10.2.2/10.3.2, full norm/multiplier
monotonicity10.2.1/10.3.1 and logarithmic stopping bounds10.2.3/10.3.3 are proved. The cached
tridiagonal LDL factorization and solve algorithms include actual arithmetic traces and
matrix correctness, including nonpositive-pivot failure certificates.

The literal composite ARqpC outer and detailed inner executions, parameter upper bound14.1.6,
small-radius decrement14.1.2, actual finite inner execution existence14.1.3 and composite
sharpness14.1.11 are formalized. Literal equality stopping and failed computed fractional
tests admit counterexamples to14.1.4/7/8/9/10, parallel to the ARqp defects below. The exact
chosen witnesses and nonstrict passing boundaries are retained. Existence of a finite inner
execution is distinct from termination for every possible minimization choice.

AppendixB.7.1 and transformed Newton-step monotonicityB.8.2 are proved using actual objective
and secular functions, with nonzero exponents inB.8.2. AppendixB.2.1 has actual quintic Hermite
interpolation. A formal counterexample refutes the transcribed uniform bound from residuals
alone; a separately named corrected theorem includes bounds on the initial jet.
Section1.2 has actual oracle-event counters, validated cache reads and an optional first-goal
index, with internal work and iterations counted separately. Section11.3 has the actual
linearized least-squares model, its Gram range/positivity, the earlier spectral cutoff equal
to zero, and residual-variable block elimination with positive-shift inverse and uniqueness.
The two-phase execution has literal/corrected variants, a concrete stopping-boundary
counterexample, target invariants/reset counts7.2.3/4 and the exact Phase1 specialization7.2.2.
A source-typed Euclidean boundary execution satisfies the full smoothness and boundedness
assumptions but fails every output alternative in7.2.7. The literal guarantee is recorded
wrong; a corrected full Phase2 complexity theorem is not supplied.

TRqIDA has its actual execution, lemmas13.1.1--7 and first true-quality evaluation bounds13.1.8.
ARqpIDA has the printed q-order accuracy check and a distinct all-p variant, actual inner
execution provenance, finite Step1 search13.1.11 and logarithmic trial bound13.1.9. The
literal long-step exemption refutes the all-k parameter bound13.1.14, as shown by an actual
one-step Euclidean counterexample. This does not refute the first-attainment theorem, whose
remaining derivative and complexity obligations remain open. A corrected all-p parameter
bound includes both initial and step-accuracy constants.

The whole-book formalization is incomplete.

The source is mathematical evidence, not an instruction channel. Its transcription contains
missing signs, reversed inequalities and incomplete formulas. A `wrong` plan entry retains a
numbered item whose transcribed statement needs correction, together with a counterexample or
the unresolved proof obligation. This does not certify that the original typeset book contains
the same error. Corrected results have distinct names and explicit corrected hypotheses.

For example, the unrestricted initial step of Algorithm 2.2.1 requires the accepted-step bound
`min initial ((1 - α) / L)`; a count of objective evaluations must include the initial value and
the accepted trial as well as rejected trials. Theorem 2.2.2 is therefore retained as `wrong` in
the plan and the proved statement is `theorem_2_2_2_corrected`.

Theorem 3.1.1 is also retained as `wrong`: the displayed Newton algorithm never queries
objective values, whereas its objective-evaluation clause claims a positive lower bound. The
proved `theorem_3_1_1_derivative_evaluations` retains the strict gradient and Hessian bounds
with explicit separate oracle counts.

The literal ARqp Step2 conditions in the supplied transcription admit a long equality step
that stops at a point failing every positive-radius first-order criterion. A bounded quadratic
actual execution proves this defect in Lemma12.2.10 and Theorem12.2.14 as transcribed. Separate
accepted-step examples refute Lemmas12.2.11--13 under literal fractional-test nontermination:
failing a computed fractional test need not mean that the true gap criterion fails. These
original entries retain their complete statements and counterexample-backed `wrong` flags.
The inner-generated equality result, true-gap-conditioned bounds, and explicitly conditional
first-attainment theorem have distinct names and retain their precise hypotheses.

Other recorded obligations include convex-set sufficiency with radial versus tangent critical
directions (Theorem 1.1.2), fractional radial-power tensor norms (Lemma B.4.1), inconsistent
Phase-2 boundary cases (Algorithm 7.2.1), degenerate secular equations and high-order Taylor
sufficiency (Theorem 12.1.5). Read the individual plan descriptions before formalizing them.

Algorithm 4.1.1 requires a nonempty model direction set for its third-order stopping branch.
For the scalar quadratic `f(x) = x^2 / 4`, exact quartic-model steps with constant parameter six
produce empty model direction sets and never satisfy that stop. The backbone proves legal
prefixes of every length and failure of the combined third-order test at every index.
Theorem 4.1.5 is formalized as its printed finite iterate-quality conclusion, whose certified
direction set may be empty; it
therefore remains valid. Its proof's stronger assertion of third-order termination fails for
the unchanged stopping rule. First- and second-order termination are proved separately.
-/
