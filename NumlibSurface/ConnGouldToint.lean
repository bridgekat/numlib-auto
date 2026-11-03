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
import NumlibSurface.ConnGouldToint.Chapter16

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
A counterexample disproves equality with the derivative of the composite in general.


Chapter 4 covers structured systems and projections. The Woodbury formula requires the
middle inverse. The Cholesky conversion uses L D^(1/2), the row space is the range of Aᵀ,
and uniqueness in the reduced quadratic problem requires positive-definite curvature.
For (4.4.8), an augmented-system solution yields the weighted projection.

Chapter 5 covers CG and PCG estimates, Krylov growth, and normal-equation residuals.
The CG bounds are expressed in product form to include exact initial iterates.

Chapters 6 and 8 cover the basic trust-region iteration, Cauchy model decrease,
and dual-norm estimates. In the proof of Theorem 6.4.3 the explicit radius lower bound
also includes the initial radius. For Theorem 8.1.8, uniform norm equivalence alone
does not imply AN.3. A scaling counterexample and a fixed-norm version with Lipschitz
gradients along the iterates are formalized.

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


Theorem 9.1.1 requires a positive ball radius. A radius-zero counterexample shows that
validity at the center alone gives no gradient bound.

Chapter 10 covers cumulative model decrease for the nonmonotone acceptance rule.
The reference schedule in (10.1.2) requires strict decrease only when the reference changes.

Chapter 11 covers Clarke steepest descent using the support identity proved in (3.1.4).
Pointwise smooth model matching does not give the uniform decrease in Lemma 11.1.3
or Corollary 11.1.4. The corrected results require a uniform one-sided first-order
model estimate near a nonstationary point.
Lemmas 11.2.2 and 11.2.3 also require uniform control of the normalized error. A compact
parameter counterexample shows that pointwise agreement alone permits small-radius rejections.



Section 12.1 covers box projection, the projected-gradient path, and the criticality measure.
In (12.1.3), the radial formula applies outside the closed ball. Points inside project to
themselves.

Chapter 13 covers the logarithmic barrier. AC.8 holds for uniformly bounded positive paths.
On an unbounded approach to the boundary, a growing coordinate can cancel a vanishing one.

Chapter 14 covers the quadratic penalty and first-order multiplier estimate. In (14.2.3),
both derivatives in the stationarity condition are evaluated at the feasible point.

Chapter 16 covers the uniform least-squares Hessian bound, exact minimization of the scalar
epigraph merit function, and the Fischer–Burmeister residual formulation of complementarity.
Equation (16.2.24) gives a real minimum value. The argmin is the singleton containing that value.
-/
