import NumlibSurface.ConnGouldToint.Chapter02
import NumlibSurface.ConnGouldToint.Chapter03
import NumlibSurface.ConnGouldToint.Chapter04
import NumlibSurface.ConnGouldToint.Chapter05
import NumlibSurface.ConnGouldToint.Chapter06
import NumlibSurface.ConnGouldToint.Chapter07
import NumlibSurface.ConnGouldToint.Chapter08
import NumlibSurface.ConnGouldToint.Chapter09
import NumlibSurface.ConnGouldToint.Chapter10
import NumlibSurface.ConnGouldToint.Chapter11
import NumlibSurface.ConnGouldToint.Chapter12
import NumlibSurface.ConnGouldToint.Chapter13
import NumlibSurface.ConnGouldToint.Chapter14
import NumlibSurface.ConnGouldToint.Chapter15
import NumlibSurface.ConnGouldToint.Chapter16
import NumlibSurface.ConnGouldToint.Chapter17

/-!
# Conn–Gould–Toint, *Trust-Region Methods*

The surface library for Andrew R. Conn, Nicholas I. M. Gould, and Philippe L. Toint's
*Trust-Region Methods* [conn2000trust]. The book develops trust-region methods for unconstrained
and constrained optimization, together with methods for solving the subproblems and applications
to nonlinear equations.

Chapter 2 covers eigenpairs, matrix decompositions, and vector and matrix norms. The
Gershgorin discs cover the spectrum by their union. A diagonal counterexample rules out
the printed intersection claim.

Chapter 3 covers Taylor estimates, unconstrained optimality, and convergence rates. The Q-rate
definitions use the successor error to the limit, correcting the printed successive difference.
Theorem 3.3.2 includes the Kantorovich ball condition. A small correction can otherwise
take the first step outside the domain.
The Clarke composite rule in Corollary 3.2.13 uses the outer support bound.
Theorem 3.2.8 uses nonempty compact feasible fibers and gives continuity of
the minimum value and upper hemicontinuity of the optimizer correspondence.
Separate examples show why the printed continuity claims need these changes.
The normal and positive tangent cones in Theorem 3.2.10 are continuous on
fixed active faces in the bounded-section sense. Theorem 3.2.7 has the
locally unique strict-local-minimizer branch with mixed active-set persistence.
The proof assumes an explicit smooth active KKT residual and its block derivative.
Theorem 3.2.15 uses local Lipschitz outer functions and a strict Clarke
descent direction for an active constraint. A boundary example shows why
the printed outer-domain conditions are insufficient.
A counterexample disproves equality with the derivative of the composite in general.


Chapter 4 covers structured systems and projections. The Woodbury formula requires the
middle inverse. The Cholesky conversion uses L D^(1/2), the row space is the range of Aᵀ,
and uniqueness in the reduced quadratic problem requires positive-definite curvature.
For (4.4.8), an augmented-system solution yields the weighted projection.

Chapter 5 covers CG and PCG estimates, Krylov growth, and normal-equation residuals.
The CG bounds are expressed in product form to include exact initial iterates.
Lemma 5.1.5 needs nonzero residual pairings at the earlier directions as well as the last.
The identity-Hessian counterexample shows what fails when an earlier line step is zero.


Chapters 6 and 8 cover the basic trust-region iteration, Cauchy model decrease,
and dual-norm estimates. In the proof of Theorem 6.4.3 the explicit radius lower bound
also includes the initial radius. Theorem 6.3.3 uses the first actual Armijo
acceptance. A sufficient length cutoff guarantees termination, and the
failed predecessor gives the decrease bound.
In Section 6.5, the corrected ratio estimates
assume uniform Hessian control on the trial segments. Theorem 6.5.5 also
assumes local model curvature along those segments to keep the iterates near
the limiting point. Section 6.6 proves the eigenpoint decrease and the
second-order convergence results. Lemma 6.6.6 treats a rejected trial by
following the unchanged iterate to its first successful trial and bounding
the radius at that trial. Theorem 6.6.4 uses uniform objective Hessian
variation on small trial segments. Theorem 8.1.4 takes first-order convergence
as an input. In Theorem 8.1.5, local persistence of negative model curvature
is assumed for the scaled-curvature liminf. The objective-curvature conclusion
holds without that extra hypothesis. For Theorem 8.1.8, uniform norm equivalence alone
does not imply AN.3. A scaling counterexample and a fixed-norm version with Lipschitz
gradients along the iterates are formalized. Theorem 8.1.9 uses a steepest
direction in the trust-region norm. The Euclidean ray can fail the claimed
decrease, as the checked counterexample shows. The radius bound in Theorem 8.4.4
includes the scaled initial radius. Theorem 8.4.8 uses eventual model convexity
on trial segments throughout a neighborhood of the limit. Section 8.5 makes
the center agreement and outer derivative bounds explicit, and gives a
polynomial counterexample showing why constituent Hessian bounds are needed.

Chapter 7 covers quadratic subproblems on spheres and balls and properties of Lanczos
tridiagonals. The sphere and ball characterizations require a positive radius. Theorem 7.5.12
expresses the exclusion of the hard case through eigenvector nonorthogonality. Theorem 7.5.16
uses the preconditioner inner-product coordinates.
The Moré–Sorensen iteration allows exact arrival at the root. The sufficient objective
acceptance coefficient in the stopping rules is an upper bound on the chosen coefficient.
For Theorem 7.3.4, the convergence phases are formalized separately. A fixed leftmost
eigenvector and a continuous boundary correction give vector convergence in the hard case.
The original direction-selection guarantee and the complete safeguarded algorithm remain open.
Weighted subproblems use the M-inner product or the explicit coordinate transformation.
The nonnegative index in Lemma 7.5.8 is k. Theorem 7.5.9 covers stationary
stops and both positive- and zero-curvature boundary stops for convex
quadratics. At zero curvature, the model decreases affinely along the
last search ray.


In Algorithm 9.1.1, the selected trial can reset the reference while the original
trial still triggers contraction. A bounded-below quadratic example makes every
iteration successful and every current model invalid, with radii tending to zero.
The corrected convergence analysis retains the current radius on invalid low-ratio
iterations and contracts only after model validity has been certified.
The subsequence conclusion of Theorem 9.2.5 uses infinitely many successful
iterations and compact containment. The limit-inferior conclusion needs neither.
Theorem 9.1.1 requires a positive ball radius. A radius-zero counterexample shows that
validity at the center alone gives no gradient bound. Theorem 9.3.1 also needs
a positive radius. Centered Taylor differences give the Hessian estimate even
when the model and objective values at the center differ. In (9.3.4), the
model Hessian need only have a lower curvature bound tending to zero.
Theorem 9.3.3 uses this bound to establish second-order criticality in the limit.
The Newton interpolation construction in Section 9.4 uses a simplex lattice
to produce a complete, uniformly bounded graded polynomial basis. In (9.4.5),
the normalization divides by the signed pivot to produce a unit diagonal. The model
error estimate uses affine reproduction and uniform bounds on all Newton
blocks on the ball. A five-point incomplete quadratic example satisfies the
printed adjacent-block and final-block bounds and violates (9.4.21) for every
proposed uniform constant.
In Section 9.5 the memory estimate uses the bound on past models at the
last accepted center. The quadratic error proof controls the product of
recent weights using the adjacent radius lower factor, allowing radii to
vary during a rejected block.

Chapter 10 covers cumulative model decrease for the nonmonotone acceptance rule.
The reference schedule in (10.1.2) requires strict decrease only when the reference changes.
The accepted count in (10.1.11) includes iteration zero. The convergence proofs
exclude an eventual positive gradient floor and use uniform gradient continuity
from the bounded objective Hessian.
In Section 10.2, the ratio and element-fit tests in (10.2.6)–(10.2.7) are
equivalent when the individual predicted decrease is strictly positive.
At zero predicted decrease the two tests can give different answers.
The radius lower bound compares the fit tolerances directly and uses the
sum of the element curvature bounds. Theorem 10.2.6 requires the uniform
norm comparison from AN.1.
Section 10.3 embeds integer-indexed line search in the exact trust-region
model and verifies the gradient-angle and positive-curvature CG estimates.
Theorem 10.3.4 requires Euclidean ball geometry. A diamond gives a
counterexample under norm comparison alone.
Section 10.4 uses augmented predicted decrease for the corrected step ratio.
Section 10.6 uses a vanishing tolerance schedule and an eventual curvature
margin for the second-order dynamic accuracy test.

Chapter 11 covers Clarke steepest descent using the support identity proved in (3.1.4).
The nonsmooth radius update caps the expansion lower bound in (11.1.16) at the
maximum radius, which avoids an empty interval. A zero predicted decrease is
treated as rejection.
Pointwise smooth model matching does not give the uniform decrease in Lemma 11.1.3
or Corollary 11.1.4. The corrected results require a uniform one-sided first-order
model estimate near a nonstationary point.
Lemmas 11.2.2 and 11.2.3 also require uniform control of the normalized error. A compact
parameter counterexample shows that pointwise agreement alone permits small-radius rejections.
Section 11.3 proves convergence for nonmonotone and composite correction
steps under uniform normalized agreement and an explicit Euclidean step bound.
Section 11.4 derives the Clarke support formulas for clipped residuals and
the active-gradient convex hull for a finite affine maximum.
Section 11.5 establishes uniform Taylor model accuracy from quadratic
remainder bounds. A scalar example shows why the modeled residual must
also lie in the outer function’s Lipschitz domain.



Section 12.1 covers box projection, the projected-gradient path, and the criticality measure.
In (12.1.3), the radial formula applies outside the closed ball. Points inside project to
themselves.

The corrected Theorem 12.2.1 uses model-gradient agreement at the base point.
Opposite gradients can make every positive trial fail the upper decrease test.
A critical starting point can be returned before computing the initial trial
parameter. The generalized Cauchy decrease includes the tangent stopping test.
Lemma 12.3.1 uses local constancy to cover connected sets. Lemma 12.3.6
approximates the negative gradient by normal directions at nearby points.
The perturbation result identifies the active set from nearby supported normal
representations. Lemma 12.3.7 and Theorem 12.3.8 have versions under asymptotic
normal certificates. Corollary 12.3.9 assumes eventual identification.
The local comparison in the proof of Theorem 12.3.4 uses the relaxed
feasible set and a shifted displacement. A half-line example shows why
the comparison cannot give the full-feasible bound from the trial
conditions alone. The full run-based identification result remains open.
Section 12.4 makes the identified-face trapping, feasible extension, and
trial-segment Hessian agreement explicit. The corrected generalized eigenpoint
test and decrease bound use the sign appropriate to negative curvature.
A cubic model shows that the printed test can accept a strict increase.

Chapter 13 covers the logarithmic barrier. Theorem 13.2.1 uses a lower objective
bound to bound the barrier along the run. For log barriers, AC.8 holds on
uniformly bounded positive paths.
The curvature limit superior in Theorem 13.4.2 supplies arbitrarily late
qualifying indices. The full inner-algorithm justification remains open.
The strong-criticality counterexample in Section 13.4 uses a smooth cutoff
to meet the lower-boundedness requirement that the printed quadratic fails.
On an unbounded approach to the boundary, a growing coordinate can cancel a vanishing one.
The log-barrier Hessian is diagonal and uniformly bounded away from the boundary.
The quadratic model uses the exact second-order Taylor data.
Section 13.3 proves the constrained Cauchy and eigenpoint decrease bounds
in the common Euclidean norm. Corollary 13.3.2 uses the corrected boundary
separation hypothesis of Theorem 13.2.1.
In Algorithm 13.6.1 the quadratic barrier model term has a positive sign
and the trial point must be feasible. Explicit scalar examples show why
the printed sign and unsigned distance test need these corrections.
Theorem 13.6.2 derives finite stopping from the inner limits with bounded
primal coordinates. An explicit all-successful scalar run with globally
smooth objective and uniformly bounded Hessian has unbounded primal
coordinates and never satisfies the complementarity test. The full inner
limit argument under the corrected assumptions remains open.
The safeguard analysis in Theorem 13.6.4 uses arbitrarily late successful
iterations to derive AA.8 from vanishing steps. Its proof bounds the
projection error directly without requiring the projection to become inactive.
The corrected primal scaling theorem in Section 13.7 retains the
gradient-tolerance rate from the primal-dual theorem. A one-dimensional
quadratic example shows why vanishing scaled tolerances alone are insufficient.
Section 13.9 interprets complementarity as a vector residual and takes the
Hessian infimum over unit directions, as in the proof. Complementarity alone
controls the barrier curvature on the free rows of the Jacobian.
Section 13.10 compares the affine-slice and ambient clearances in
projected-normal coordinates, with an explicit feasibility check.
Section 13.11 states the scaled gradient convergence theorem with the
uniform scaled-curvature bound expressed directly.
Section 13.12 covers first-order and weak second-order stationarity under affine scaling.
The corrected Cauchy decrease in Theorem 13.12.3 includes a fraction-to-boundary cap.
A one-dimensional example violates the printed bound for every positive criticality cap.
Theorem 13.12.5 gives positive decrease at the eigenpoint, with a feasibility cap
covering every coordinate that decreases along the chosen ray.
Theorem 13.12.4 proves scaled gradient convergence for the corrected run.
Theorem 13.12.6 transfers vanishing scaled model curvature error to weak
second-order stationarity on the active face. The version-two run must
still supply the curvature error bound.



Chapter 14 covers the quadratic penalty and first-order multiplier estimate. In (14.2.3),
both derivatives in the stationarity condition are evaluated at the feasible point.

The multiplier difference in (14.2.26) has the sign from (14.2.6).
In (14.3.15), the scaling factor is μ/ν − 1. At an infeasible point,
the Lagrangian Hessian term in Lemma 14.3.2 can grow as the penalty
parameter tends to zero. The corrected extreme-eigenvalue estimates
bound that term explicitly. The nullspace limit uses the entire constraint
kernel and the fixed-multiplier Hessian, which agrees with the required
penalty term at a feasible point.
Section 14.4 corrects the multiplier sign and handles every permitted
penalty update between multiplier changes. Theorem 14.4.2 makes AA.9
explicit. Section 14.5 uses a strict exact-penalty threshold and a
surjective residual derivative in the multiplier bound. Section 14.6
proves second-order equivalence and uses the printed Hessian formula
at feasible points, where its omitted term vanishes.

Chapter 15 covers local SQP convergence. Theorem 15.2.1(i) needs supplied multipliers
to stay near the root multiplier from the first iteration. A convergent multiplier
sequence can otherwise make the first stationary subproblem inconsistent.
Section 15.3 uses a distance penalty and explicit chain-rule, restoration, and
Taylor estimates. A C² example violates the printed quadratic Newton estimate
without additional Hessian regularity. The corrected merit ratio requires
positive primal error.
The composite SQP analysis evaluates the normal-step estimate at the Cauchy
step and uses Lipschitz control along the full trial segments. The radius
argument in Theorem 15.4.6 uses the very-successful update. The corrected
coefficient in Lemma 15.4.9 stays positive for every nonnegative model bound.
Theorem 15.4.10 includes the Cauchy coefficient in the radius threshold and
the initial tail radius in the floor. Theorem 15.4.11 makes the required
uniform control of accepted-step variation explicit. The two cases in (15.4.140)
give a common lower bound using the smaller coefficient. In (15.4.142),
the second entry of the minimum uses the reciprocal of the rank constant.
Theorem 15.4.12 separates original-trial agreement from corrected accepted
decrease. The local rate result uses eventual accepted-step conditions and
multiplier convergence. Theorem 15.4.16 uses the maximum cluster curvature
and requires the cluster set to control the tail, as relative compactness ensures.
Theorems 15.4.22–25 treat the Byrd–Omojokun method with corrected steps.
Theorem 15.4.23 corrects the printed algorithm reference, and Theorem 15.4.25
uses the maximum cluster curvature.
Section 15.5 uses Pareto deletion so earlier filter exclusions survive.
The printed margin-based deletion admits a bounded insertion stream
with violations bounded away from zero. Strict rejection shrinkage
prevents the verified smooth nonstationary stalling trace.

Chapter 16 covers the uniform least-squares Hessian bound, exact minimization of the scalar
epigraph merit function, and the Fischer–Burmeister residual formulation of complementarity.
Section 16.3 uses the direction-to-residual Jacobian in (16.3.4), transposing the
printed column-gradient matrix to agree with (16.3.8)–(16.3.9). The merit
derivative also holds at simultaneous zeros of the residual arguments.
At a residual root in Theorem 16.1.4, the Jacobian must be injective for positive
definiteness. Even with regular roots of a square system and exact residual models, a BTR
run can alternate between roots. The eventual model-root result uses convergence
of the iterates and a trust region containing a fixed positive-radius ball.
In (16.2.15), the epigraph Lagrangian Hessian sums over residual components,
or equivalently weights the Hessians of the affine branches.
Equation (16.2.24) gives a real minimum value. The argmin is the singleton containing that value.

Chapter 17 covers parameter and initial-radius choices. In (17.1.3), the factor
1 − η₂ multiplies the common value and slope only. In (17.2.2), the radius is
the ray parameter multiplied by the gradient norm. Both discrepancies are in print.
The initial probe safeguards use a fallback strictly below one when shrinking.
In (17.4.9), the projected trial point subtracts the Lagrangian gradient. The printed
sign of the equality multiplier contribution would instead subtract it twice relative
to stationarity, as the identity-projection counterexample shows.



-/
