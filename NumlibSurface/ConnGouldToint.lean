import NumlibSurface.ConnGouldToint.Chapter03
import NumlibSurface.ConnGouldToint.Chapter05
import NumlibSurface.ConnGouldToint.Chapter06
import NumlibSurface.ConnGouldToint.Chapter07
import NumlibSurface.ConnGouldToint.Chapter08
import NumlibSurface.ConnGouldToint.Chapter10
import NumlibSurface.ConnGouldToint.Chapter12
import NumlibSurface.ConnGouldToint.Chapter14
import NumlibSurface.ConnGouldToint.Chapter16

/-!
# Conn–Gould–Toint, *Trust-Region Methods*

The surface library for Andrew R. Conn, Nicholas I. M. Gould, and Philippe L. Toint's
*Trust-Region Methods* [conn2000trust]. The book develops trust-region methods for unconstrained
and constrained optimization, together with methods for solving the subproblems and applications
to nonlinear equations.

Chapter 3 covers Taylor estimates, unconstrained optimality, and convergence rates. The Q-rate
definitions use the successor error to the limit, correcting the printed successive difference.
Theorem 3.3.2 includes the Kantorovich ball condition. A small correction can otherwise
take the first step outside the domain.

Chapter 5 covers CG and PCG estimates, Krylov growth, and normal-equation residuals.
The CG bounds are expressed in product form to include exact initial iterates.

Chapters 6 and 8 cover the basic trust-region iteration, Cauchy model decrease,
and dual-norm estimates. In the proof of Theorem 6.4.3 the explicit radius lower bound
also includes the initial radius. For Theorem 8.1.8, uniform norm equivalence alone
does not imply AN.3. A scaling counterexample and a fixed-norm version with Lipschitz
gradients along the iterates are formalized.

Chapter 7 covers quadratic subproblems on spheres and balls and properties of Lanczos
tridiagonals. The sphere and ball characterizations require a positive radius. Lemma 7.5.11
is given for symmetric tridiagonals as used by Lanczos, and Theorem 7.5.12 expresses the
exclusion of the hard case through eigenvector nonorthogonality.

Chapter 10 covers cumulative model decrease for the nonmonotone acceptance rule.
The reference schedule in (10.1.2) requires strict decrease only when the reference changes.

Chapter 12 covers the projected-gradient path. In (12.1.3), the radial projection
formula applies outside the closed ball, and points inside project to themselves.

Chapter 14 covers the quadratic penalty and first-order multiplier estimate. In (14.2.3),
both derivatives in the stationarity condition are evaluated at the feasible point.

Chapter 16 covers the uniform least-squares Hessian bound, exact minimization of the scalar
epigraph merit function, and the Fischer–Burmeister residual formulation of complementarity.
Equation (16.2.24) gives a real minimum value. The argmin is formalized as the singleton set containing that value.
-/
