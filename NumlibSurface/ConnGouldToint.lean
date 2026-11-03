import NumlibSurface.ConnGouldToint.Chapter06
import NumlibSurface.ConnGouldToint.Chapter08
import NumlibSurface.ConnGouldToint.Chapter16

/-!
# Conn–Gould–Toint, *Trust-Region Methods*

The surface library for Andrew R. Conn, Nicholas I. M. Gould, and Philippe L. Toint's
*Trust-Region Methods* [conn2000trust]. The book develops trust-region methods for unconstrained
and constrained optimization, together with methods for solving the subproblems and applications
to nonlinear equations.

Chapters 6 and 8 cover the basic trust-region iteration, Cauchy model decrease,
and dual-norm estimates. In the proof of Theorem 6.4.3 the explicit radius lower bound
also includes the initial radius. For Theorem 8.1.8, uniform norm equivalence alone
does not imply AN.3. A scaling counterexample and a fixed-norm version with Lipschitz
gradients along the iterates are formalized.

Chapter 16 covers exact minimization of the scalar epigraph merit function and the
Fischer–Burmeister residual formulation of complementarity. In (16.2.24), the minimum value is a real
number and the argmin is formalized as the singleton set containing that number.
-/
