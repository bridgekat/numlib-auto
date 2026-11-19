/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Boundary.Kernel
import Numlib.Analysis.Sobolev.Boundary.PolygonTrace
import Numlib.Analysis.Sobolev.Density
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.Analysis.Sobolev.ExtensionHigher
import Numlib.Analysis.Sobolev.HolderEmbedding
import NumlibSurface.AtkinsonHan.Chapter07.Section02

/-!
# Atkinson and Han, Section 7.3: Density, extensions, embeddings, traces and equivalent norms

This module formalizes Section 7.3 of [han2009theoretical], on the Sobolev spaces $W^{k,p}(\Omega)$
of an open set $\Omega$. Smooth functions are dense: $C^\infty(\Omega) \cap W^{k,p}(\Omega)$ is
dense in $W^{k,p}(\Omega)$ for every open $\Omega$ (Meyers–Serrin, Theorem 7.3.1),
$C^\infty(\overline\Omega)$ is dense on a regular domain (Theorem 7.3.2), $W_0^{k,p}(\Omega)$ is the
closure of $C_0^\infty(\Omega)$ (Theorem 7.3.3), and $C_0^\infty(\mathbb{R}^d)$ is dense in
$W^{k,p}(\mathbb{R}^d)$ (Theorem 7.3.4), all for $1 \le p < \infty$. A regular domain has a bounded
extension operator $W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$ (Theorem 7.3.5). With the
continuous embedding $V \hookrightarrow W$ and the compact embedding
$V \hookrightarrow\hookrightarrow W$ of Definition 7.3.6, the module states the Sobolev embedding
theorem (Theorem 7.3.7), the Rellich–Kondrachov theorem (Theorem 7.3.8) and $W^{k,p}(\Omega)
\hookrightarrow\hookrightarrow W^{l,p}(\Omega)$ for $l < k$ (Theorem 7.3.9).

On a bounded $C^1$ domain and on a triangulated polygon, the trace
$\gamma : W^{1,p}(\Omega) \to L^p(\Gamma)$, $\Gamma = \partial\Omega$, is bounded, extends the
restriction $v \mapsto v|_\Gamma$, and is compact for $1 < p < \infty$ (Theorem 7.3.10); its kernel
is $W_0^{1,p}(\Omega)$. On $W^{2,p}(\Omega)$ the traces $\gamma_0 v = v|_\Gamma$ and
$\gamma_1 v = \partial v / \partial\nu$ are the unique bounded operators into $L^p(\Gamma)$ with
these values on smooth functions (Theorem 7.3.11, the case $s = 2$). The Deny–Lions theorems give
norms on $W^{k+1,p}(\Omega)$ of the form $|v|_{k+1,p,\Omega} + \sum_j f_j(v)$ that are equivalent to
$\|v\|_{k+1,p,\Omega}$ (Theorems 7.3.12–7.3.14). They yield the Poincaré–Friedrichs inequalities
(Examples 7.3.15 and 7.3.16) and the equivalence of $|v|_{k+1,p,\Omega}$ with the norm of the
quotient space $W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$ (Theorem 7.3.17 and Corollary 7.3.18). The
proofs specialize `Numlib.Analysis.Sobolev.Density`, `Numlib.Analysis.Sobolev.ExtensionHigher`,
`Numlib.Analysis.Sobolev.EmbeddingDomain`, `Numlib.Analysis.Sobolev.HolderEmbedding`,
`Numlib.Analysis.Sobolev.DenyLions`, `Numlib.Analysis.Sobolev.Boundary.ContDiffDomain`,
`Numlib.Analysis.Sobolev.Boundary.Kernel` and `Numlib.Analysis.Sobolev.Boundary.PolygonTrace`, with
the vocabulary of `Numlib.Analysis.Normed.Operator.Embedding`.

## Main definitions

* Definition 7.3.6, `AtkinsonHan.Chapter07.definition_7_3_6`: the continuous embedding
  $V \hookrightarrow W$ along an injective linear map with $\|\iota v\|_W \le c \|v\|_V$ (7.3.1).
* Definition 7.3.6, `AtkinsonHan.Chapter07.definition_7_3_6_compact`: the compact embedding
  $V \hookrightarrow\hookrightarrow W$, a continuous embedding that maps bounded sequences to
  sequences with a convergent subsequence.
* Theorem 7.3.11, `AtkinsonHan.Chapter07.theorem_7_3_11_trace₀`: the trace
  $\gamma_0 : W^{2,p}(\Omega) \to L^p(\Gamma)$.
* Theorem 7.3.11, `AtkinsonHan.Chapter07.theorem_7_3_11_trace₁`: the normal-derivative trace
  $\gamma_1 v = \sum_i \nu_i \, \gamma(\partial_i v)$ from $W^{2,p}(\Omega)$ to $L^p(\Gamma)$.
* Equation (7.3.3), `AtkinsonHan.Chapter07.equation_7_3_3`: the quantity
  $|v|_{k,p,\Omega} + \sum_j f_j(v)$.
* Equation (7.3.4), `AtkinsonHan.Chapter07.equation_7_3_4`: the quantity
  $[|v|_{k,p,\Omega}^p + \sum_j f_j(v)^p]^{1/p}$.

## Main results

* Theorem 7.3.1, `AtkinsonHan.Chapter07.theorem_7_3_1`: (Meyers–Serrin) every
  $v \in W^{k,p}(\Omega)$, $1 \le p < \infty$, is a limit of functions in
  $C^\infty(\Omega) \cap W^{k,p}(\Omega)$.
* Theorem 7.3.2, `AtkinsonHan.Chapter07.theorem_7_3_2`: on a $W^{1,p}$-extension domain,
  $1 \le p < \infty$, every $v \in W^{1,p}(\Omega)$ is a limit of restrictions of functions in
  $C_c^\infty(\mathbb{R}^d)$.
* Theorem 7.3.2, `AtkinsonHan.Chapter07.theorem_7_3_2_higher`: the same at every order $k$, on a
  $W^{k,p}$-extension domain.
* Theorem 7.3.3, `AtkinsonHan.Chapter07.theorem_7_3_3`: every $v \in W_0^{k,p}(\Omega)$ is a limit
  in $W^{k,p}(\Omega)$ of functions in $C_0^\infty(\Omega)$.
* Theorem 7.3.4, `AtkinsonHan.Chapter07.theorem_7_3_4`: $C_0^\infty(\mathbb{R}^d)$ is dense in
  $W^{k,p}(\mathbb{R}^d)$ for $1 \le p < \infty$.
* Theorem 7.3.5, `AtkinsonHan.Chapter07.theorem_7_3_5`: a bounded $C^1$ domain has a bounded linear
  extension operator $W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^{d+1})$ for each $p \in [1, \infty]$.
* Theorem 7.3.5, `AtkinsonHan.Chapter07.theorem_7_3_5_order`: a bounded $C^k$ domain has a bounded
  linear extension operator $W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$ for each
  $p \in [1, \infty]$.
* Theorem 7.3.5, `AtkinsonHan.Chapter07.theorem_7_3_5_order_lp`: the extension operator of order $k$
  can be chosen bounded also from $L^p(\Omega)$ to $L^p(\mathbb{R}^{d+1})$.
* Theorem 7.3.5, `AtkinsonHan.Chapter07.theorem_7_3_5_order_uniform`: at a fixed order $k$, one map
  on functions gives a bounded extension operator for every $p \in [1, \infty]$.
* Definition 7.3.6, `AtkinsonHan.Chapter07.definition_7_3_6_of_compact`: a compact embedding is a
  continuous embedding.
* Theorem 7.3.7, `AtkinsonHan.Chapter07.theorem_7_3_7`: the Sobolev embedding theorem, clauses
  (a)–(c).
* Theorem 7.3.7(a), `AtkinsonHan.Chapter07.theorem_7_3_7_a`: if $k < (d+1)/p$, then
  $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ for $q \le p^*$, $1/p^* = 1/p - k/(d+1)$.
* Theorem 7.3.7(b), `AtkinsonHan.Chapter07.theorem_7_3_7_b`: if $k = (d+1)/p$, then
  $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ for $q < \infty$.
* Theorem 7.3.7(c), `AtkinsonHan.Chapter07.theorem_7_3_7_c`: if $k > (d+1)/p$ and $(d+1)/p$ is not
  an integer, then $W^{k,p}(\Omega) \hookrightarrow C^{k - [(d+1)/p] - 1, \beta}(\overline\Omega)$
  with $\beta = [(d+1)/p] + 1 - (d+1)/p$.
* Theorem 7.3.7(c), `AtkinsonHan.Chapter07.theorem_7_3_7_c_integer`: if $(d+1)/p = \ell$ is an
  integer and $k > \ell$, then $W^{k,p}(\Omega) \hookrightarrow C^{k - \ell - 1,
  \beta}(\overline\Omega)$ for every $\beta \in (0, 1)$.
* Theorem 7.3.8, `AtkinsonHan.Chapter07.theorem_7_3_8`: the Rellich–Kondrachov theorem, clauses
  (a)–(c), with the target $C(\overline\Omega)$ in (c).
* Theorem 7.3.8(a), `AtkinsonHan.Chapter07.theorem_7_3_8_a`: if $1 \le k < (d+1)/p$, then
  $W^{k,p}(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega)$ for $q < p^*$.
* Theorem 7.3.8(b), `AtkinsonHan.Chapter07.theorem_7_3_8_b`: as printed, if $k = (d+1)/p$, then
  $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ for $q < \infty$.
* Theorem 7.3.8(b), `AtkinsonHan.Chapter07.theorem_7_3_8_b_compact`: if $d \ge 1$ and $k = (d+1)/p$,
  then $W^{k,p}(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega)$ for $q < \infty$.
* Theorem 7.3.8(c), `AtkinsonHan.Chapter07.theorem_7_3_8_c`: if $k > (d+1)/p$, then $W^{k,p}(\Omega)
  \hookrightarrow\hookrightarrow C(\overline\Omega)$.
* Theorem 7.3.8(c), `AtkinsonHan.Chapter07.theorem_7_3_8_c_holder`: if $k > (d+1)/p$, then
  $W^{k,p}(\Omega) \hookrightarrow\hookrightarrow C^{k - [(d+1)/p] - 1, \beta}(\overline\Omega)$ for
  $0 < \beta < [(d+1)/p] + 1 - (d+1)/p$.
* Theorem 7.3.9, `AtkinsonHan.Chapter07.theorem_7_3_9`: $W^{k,p}(\Omega)
  \hookrightarrow\hookrightarrow W^{l,p}(\Omega)$ for $l < k$ and $1 \le p < \infty$.
* Theorem 7.3.9, `AtkinsonHan.Chapter07.theorem_7_3_9_top`: $W^{k,\infty}(\Omega)
  \hookrightarrow\hookrightarrow W^{l,\infty}(\Omega)$ for $l < k$.
* Theorem 7.3.10(a), (b), `AtkinsonHan.Chapter07.theorem_7_3_10`: on a bounded $C^1$ domain the
  trace is bounded from $W^{1,p}(\Omega)$ to $L^p(\Gamma)$ and equals $v|_\Gamma$ for $v$ continuous
  on $\overline\Omega$.
* Theorem 7.3.10, `AtkinsonHan.Chapter07.theorem_7_3_10_kernel`: on a bounded $C^1$ domain,
  $W_0^{1,p}(\Omega)$ is the kernel of the trace.
* Theorem 7.3.10(c), `AtkinsonHan.Chapter07.theorem_7_3_10_compact`: on a bounded $C^1$ domain the
  trace is compact for $1 < p < \infty$.
* Theorem 7.3.10(a), (b), `AtkinsonHan.Chapter07.theorem_7_3_10_polygon`: clauses (a) and (b) on a
  triangulated plane domain.
* Theorem 7.3.10(c), `AtkinsonHan.Chapter07.theorem_7_3_10_polygon_compact`: clause (c) on a
  triangulated plane domain, for $1 < p < \infty$.
* Theorem 7.3.11, `AtkinsonHan.Chapter07.theorem_7_3_11_trace₀_ae_eq`: $\gamma_0 v = v|_\Gamma$ for
  $v$ continuous on $\overline\Omega$.
* Theorem 7.3.11, `AtkinsonHan.Chapter07.theorem_7_3_11_trace₁_ae_eq`:
  $\gamma_1 v = \partial v / \partial\nu$ on $\Gamma$ for $v$ of class $C^1$.
* Theorem 7.3.11, `AtkinsonHan.Chapter07.theorem_7_3_11`: on a bounded $C^2$ domain, $\gamma_0$ and
  $\gamma_1$ are the unique bounded linear operators $W^{2,p}(\Omega) \to L^p(\Gamma)$ with these
  values.
* Theorem 7.3.12, `AtkinsonHan.Chapter07.theorem_7_3_12`: (Deny–Lions) on a connected domain,
  (7.3.3) and (7.3.4) are norms equivalent to $\|v\|_{k+1,p,\Omega}$ when no nonzero polynomial of
  degree $\le k$ is annihilated by all $f_j$.
* Theorem 7.3.13, `AtkinsonHan.Chapter07.theorem_7_3_13`: the same without connectedness, when
  $|v|_{k+1,p,\Omega} = 0$ and $f_j(v) = 0$ for all $j$ force $v = 0$.
* Theorem 7.3.14, `AtkinsonHan.Chapter07.theorem_7_3_14`: the same on a union of connected open
  sets, with the polynomial condition on each piece.
* Example 7.3.15, `AtkinsonHan.Chapter07.example_7_3_15`: the Poincaré–Friedrichs inequality
  (7.3.10), $\|v\|_{1,\Omega} \le c \, |v|_{1,\Omega}$ on $H_0^1(\Omega)$.
* Example 7.3.15, `AtkinsonHan.Chapter07.example_7_3_15_boundary`: $\|v\|_{1,\Omega} \le c \,
  (|v|_{1,\Omega} + \int_\Gamma |\gamma v| \, d\sigma)$ on $H^1(\Omega)$.
* Example 7.3.16, `AtkinsonHan.Chapter07.example_7_3_16`: the Poincaré–Friedrichs inequality on
  $H^1_{\Gamma_0}(\Omega)$ for an open piece $\Gamma_0$ of the boundary.
* Theorem 7.3.17, `AtkinsonHan.Chapter07.theorem_7_3_17`: on a connected domain,
  $|v|_{k+1,p,\Omega}$ is a norm on $W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$ equivalent to the
  quotient norm.
* Corollary 7.3.18, `AtkinsonHan.Chapter07.corollary_7_3_18`: the inequality (7.3.16), $\inf_{q \in
  \mathbb{P}_k(\Omega)} \|v + q\|_{k+1,\Omega} \le c \, |v|_{k+1,\Omega}$ on $H^{k+1}(\Omega)$.

## Conventions

* The ambient space of the results that need a boundary is $\mathbb{R}^{d+1}$,
  `EuclideanSpace ℝ (Fin (d + 1))`, as in Definition 7.2.1. The ratio $d/p$ of the source is
  therefore written $(d+1)/p$.
* The source states most results of the section for a bounded Lipschitz domain. Here the density,
  extension, embedding and Deny–Lions results assume that $\Omega$ is an extension domain:
  `IsSobolevExtensionDomain N p Ω` (an extension operator for $W^{1,p}$),
  `IsSobolevExtensionDomainAll N Ω` (one for every exponent) or
  `IsSobolevExtensionDomainOfOrder N k p Ω` (one for $W^{k,p}$). A bounded $C^1$ domain of
  Definition 7.2.1 is an extension domain for every exponent
  (`AtkinsonHan.Chapter07.isSobolevExtensionDomainAll_of_definition_7_2_1`), and a bounded $C^k$
  domain is a $W^{k,p}$-extension domain
  (`AtkinsonHan.Chapter07.isSobolevExtensionDomainOfOrder_of_definition_7_2_1`).
* The trace results assume a bounded $C^1$ domain, `IsContDiffDomain 1 Ω` with
  `Bornology.IsBounded Ω`, or a plane domain with a triangulation, `Triangulation Ω`.
* $\Gamma = \partial\Omega$ carries the surface measure $\sigma$, `IsContDiffDomain.boundaryMeasure`
  on a $C^1$ domain and `Triangulation.boundaryMeasure` (arclength on the boundary edges) on a
  polygon. $L^p(\Gamma)$ is `Lp ℝ p σ`, with $\sigma$ a measure on the ambient space that is carried
  by $\Gamma$.
* $W^{k,p}(\Omega)$ is `SobolevMultiIndex ℝ (stdBasis N) k p Ω volume`, with the norm of Definition
  7.2.2, except in Theorems 7.3.1, 7.3.3 and 7.3.4. Its elements are tuples of weak derivatives, and
  `SobolevMultiIndex.fn v` is the function of $v$. The seminorm $|v|_{k,p,\Omega} = (\int_\Omega
  \sum_{|\alpha| = k} |\partial^\alpha v|^p)^{1/p}$ is `SobolevMultiIndex.topSeminorm`.
* $\mathbb{P}_k(\Omega)$ is the set of the elements of $W^{k+1,p}(\Omega)$ whose function agrees
  almost everywhere on $\Omega$ with a polynomial of total degree at most $k$
  (`MvPolynomial.restrictTotalDegree`). As a subspace it is `SobolevEuclidean.polynomialSubmodule`.

## Implementation notes

* Theorems 7.3.1 and 7.3.4 use the bundled reading of Definition 7.2.2,
  `AtkinsonHan.Chapter07.definition_7_2_2`, with the norm `sobolevNorm`, and Theorem 7.3.3 uses its
  space `Sobolev ℝ k p Ω volume`. Definition 7.2.9 is formalized as the closure of the test
  functions in that space, so Theorem 7.3.3 is this closure read sequentially. The space
  $H_0^1(\Omega)$ of the Poincaré–Friedrichs inequality and of the kernel of the trace is instead
  `SobolevEuclideanZero`, the closure of the test functions in the multi-index reading. The two
  closures are not identified.
* `isCompactEmbedding_iff_isCompactOperator` identifies the compact embedding of Definition 7.3.6
  with an injective `IsCompactOperator`, so the theory of compact operators applies to it.
* Clause (c) of Theorems 7.3.7 and 7.3.8 is read on continuous representatives. A function in
  $C^{j}(\overline\Omega)$ is `ContDiffOnClosure`: of class $C^j$ on $\Omega$, with derivatives of
  order $\le j$ that extend continuously to $\overline\Omega$. The Hölder space
  $C^{j,\beta}(\overline\Omega)$ is `HolderSpace` of `Numlib.Analysis.Calculus.HolderSpace`.
* The embedding results on a domain come from the theorems on the whole space in
  `Numlib.Analysis.Sobolev.Embedding`, carried to $\Omega$ by the extension operator. Clauses (b)
  and (c) of Theorems 7.3.7 and 7.3.8 carry the hypothesis $d \ge 1$ or $p > 1$ of the backbone.
* On a $C^1$ domain the trace is Nečas's construction: the divergence theorem applied to $|v|^p w$,
  for a vector field $w$ transversal to $\Gamma$, bounds $\int_\Gamma |v|^p \, d\sigma$ by
  $C \|v\|_{1,p}^p$ for $v \in C^1(\overline\Omega)$, and the density of $C^\infty(\overline\Omega)$
  extends the trace. On a triangulated polygon the trace is glued along the boundary edges from the
  traces on the triangles.
* Boundary spaces of fractional order: `AtkinsonHan.Chapter07.definition_7_2_13` defines
  $W^{s,p}(\partial\Omega)$ relative to a chosen graph atlas only, and no theorem identifies the
  spaces of two atlases. This needs the invariance of the Slobodeckij seminorm
  $\iint |v(x) - v(y)|^p / |x - y|^{d - 1 + sp}$ under a bi-Lipschitz change of variables, applied
  to the $C^1$ chart transitions `EuclideanSpace.graphTransition` on the overlaps of two patches.
  The surface measure itself does not depend on the atlas (`GraphAtlas.measure_eq`), so the targets
  $L^p(\Gamma)$ of Theorems 7.3.10 and 7.3.11 are well defined.
* No result of the library uses the range of the trace: `AtkinsonHan.Chapter11.theorem_11_4_5` is
  stated through the density of traces in $L^1(\Gamma)$ rather than through $H^{1/2}(\Gamma)$.

## Deviations from the source

* **Theorems 7.3.2 and 7.3.5** (scope). Density uses an extension-domain hypothesis.
  For extension, the formal results treat bounded $C^k$ domains for a fixed order
  $k \ge 1$. There is one operator for all $p$ at that order. The source uses half-spaces
  and Lipschitz domains, with one operator for all orders and smoothness off the closure.
* **Definition 7.3.6** (generalization). The source assumes that $V$ and $W$ are Banach spaces; the
  definition is for normed spaces. See `AtkinsonHan.Chapter07.definition_7_3_6`.
* **Theorems 7.3.7–7.3.9** (scope). The primary embeddings are for bounded extension
  domains. The critical and Hölder cases in Theorems 7.3.7 and 7.3.8 exclude the endpoint
  $p = 1$ in dimension one.
* **Theorem 7.3.8(a)** (reading). The source leaves $k \ge 1$ implicit; at $k = 0$ the clause would
  say $L^p(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega)$ for $q < p$, which is false. See
  `AtkinsonHan.Chapter07.theorem_7_3_8_a`.
* **Theorem 7.3.8(b)** (reading). The source prints a continuous embedding, as in Theorem 7.3.7(b).
  The clause is formalized as printed and also as a compact embedding. See
  `AtkinsonHan.Chapter07.theorem_7_3_8_b` and `AtkinsonHan.Chapter07.theorem_7_3_8_b_compact`.
* **Theorem 7.3.10(c)** (correction). The source allows $1 \le p < \infty$. At $p = 1$ the trace
  maps $W^{1,1}(\Omega)$ onto $L^1(\Gamma)$ and is not compact; the library assumes
  $1 < p < \infty$. See `AtkinsonHan.Chapter07.theorem_7_3_10_compact` and
  `AtkinsonHan.Chapter07.theorem_7_3_10_polygon_compact`.
* **Theorem 7.3.11** (scope). The formal operators are traces from $W^{2,p}$ to boundary
  $L^p$ for finite $p$. The source gives higher and fractional orders, Sobolev trace
  targets and surjectivity.
* **Theorem 7.3.11** (generalization). The source asks $v \in C^1(\overline\Omega)$ for
  $\gamma_0 v = v|_\Gamma$; continuity on $\overline\Omega$ is enough. See
  `AtkinsonHan.Chapter07.theorem_7_3_11_trace₀_ae_eq`.
* **Theorem 7.3.11** (reading). The condition $v \in W^{s,p}(\Omega) \cap C^1(\overline\Omega)$ for
  $\gamma_1 v = \partial v / \partial\nu$ is read as a representative of class $C^1$ on
  $\mathbb{R}^{d+1}$. See `AtkinsonHan.Chapter07.theorem_7_3_11_trace₁_ae_eq`.
* **Theorem 7.3.14** (generalization). The source takes a disjoint union of the sets
  $\Omega_\lambda$; disjointness is not assumed. See `AtkinsonHan.Chapter07.theorem_7_3_14`.
* **Example 7.3.16** (reading). The open subset $\Gamma_0$ of $\Gamma$ is $U \cap \Gamma$ for an
  open $U \subseteq \mathbb{R}^{d+1}$, and "$v = 0$ a.e. on $\Gamma_0$" means $\gamma v = 0$
  $\sigma$-almost everywhere on $U$. See `AtkinsonHan.Chapter07.example_7_3_16`.
* **Example 7.3.16, constant** (correction). The estimate is for a fixed boundary portion.
  The constant can depend on that portion as well as the domain. A constant nonzero
  function rules out a uniform bound for boundary portions of arbitrarily small measure.

## Not formalized

* **Lipschitz domains.** The results are stated on extension domains, on bounded $C^1$ (or $C^k$,
  $C^2$) domains and on triangulated polygons. That a Lipschitz domain is an extension domain is the
  theorem of Stein or Calderón, which is not formalized, and the boundary charts of the library are
  $C^n$ graphs.
* **Theorem 7.3.5 as printed** (Stein's universal extension theorem). One operator $E$, for a
  Lipschitz domain or a half-space, bounded from $W^{k,p}(\Omega)$ to $W^{k,p}(\mathbb{R}^d)$ for
  every $k \ge 0$ and every $p \in [1, \infty]$, with $Ev$ smooth outside $\overline\Omega$. The
  reflection operator of the library has coefficients that solve a Vandermonde system of order $k$
  (`exists_vandermonde_coeffs_scales`), so it changes with $k$, and its values are not smooth
  outside $\overline\Omega$; Stein's operator is a regularization of the reflection by a Calderón
  kernel.
* **Theorems 7.3.7(b), (c) and 7.3.8(b), (c) for $d + 1 = 1$ and $p = 1$.** The backbone's form of
  Corollary 9.15 of [brezis2011functional] excludes this case.
* **Theorem 7.3.10, the range clause.** $\gamma$ maps $W^{1,p}(\Omega)$ onto
  $W^{1 - 1/p, p}(\Gamma)$, so that $H^{1/2}(\Gamma) = \gamma(H^1(\Omega))$ and the quotient norm
  (7.3.2) is equivalent to the norm of Definition 7.2.13. This is Gagliardo's theorem, and it needs
  boundary spaces of fractional order that do not depend on the atlas (see the implementation
  notes), the bound $\|\gamma v\|_{W^{1-1/p,p}(\Gamma)} \le C \|v\|_{W^{1,p}(\Omega)}$, and
  Gagliardo's right inverse.
* **Theorem 7.3.11 as printed.** On a bounded open set with $C^{k,1}$ boundary, for
  $1 \le p \le \infty$ and $s - 1/p > 1$ not an integer with $k \ge s - 1$, the maps $\gamma_0 :
  W^{s,p}(\Omega) \to W^{s - 1/p, p}(\Gamma)$ and $\gamma_1 : W^{s,p}(\Omega) \to W^{s - 1 - 1/p,
  p}(\Gamma)$ are bounded, linear and surjective. Only the $L^p(\Gamma)$ clause at $s = 2$ on a
  $C^2$ domain is formalized: the fractional targets need boundary spaces that do not depend on the
  atlas, the surjectivity needs a theorem of Gagliardo type, and the library has no $C^{k,1}$
  boundaries. The source quotes the theorem without proof.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ContDiff Distributions ENNReal NNReal Topology

namespace AtkinsonHan.Chapter07

/-! ### Definition 7.3.6: continuous and compact embeddings -/

section Embedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Definition 7.3.6** of [han2009theoretical], continuous embedding. Let $V$ and $W$ be normed
spaces over a nontrivially normed field and let $\iota : V \to W$ be linear. Then $V$ is
**continuously embedded** in $W$ along $\iota$, written $V \hookrightarrow W$, if $\iota$ is
injective and there is a constant $c$ with
$$\|\iota v\|_W \le c \, \|v\|_V \qquad \text{for all } v \in V. \tag{7.3.1}$$

**Generalization.** The source assumes that $V$ and $W$ are Banach spaces. The definition does
not need completeness, and does not impose it.

The inclusion $V \subseteq W$ of the source is an injective linear map, because the two spaces
carry different norms and the embeddings of the section are between different types. The
definition is `IsContinuousEmbedding ι`. -/
def definition_7_3_6 (ι : V →ₗ[𝕜] W) : Prop := IsContinuousEmbedding ι

/-- **Definition 7.3.6** of [han2009theoretical], compact embedding. Let $V$ and $W$ be normed
spaces and let $\iota : V \to W$ be linear. Then $V$ is **compactly embedded** in $W$ along
$\iota$, written $V \hookrightarrow\hookrightarrow W$, if $V \hookrightarrow W$ along $\iota$
and every bounded sequence $(v_n)$ in $V$ has a subsequence $(v_{n'})$ such that
$(\iota v_{n'})$ converges in $W$.

The definition is `IsCompactEmbedding ι`. By `isCompactEmbedding_iff_isCompactOperator` it is
equivalent to $\iota$ being injective and a compact operator (`IsCompactOperator`), so the
theory of compact operators applies to it.

**Reading.** Compact injective linear map expresses the compact embedding beyond Banach spaces.
-/
def definition_7_3_6_compact (ι : V →ₗ[𝕜] W) : Prop := IsCompactEmbedding ι

/-- Supporting result for **Definition 7.3.6** of [han2009theoretical]. If
$V \hookrightarrow\hookrightarrow W$ along $\iota$, then $V \hookrightarrow W$ along $\iota$:
the definition of a compact embedding includes the bound (7.3.1). -/
theorem definition_7_3_6_of_compact {ι : V →ₗ[𝕜] W} (h : definition_7_3_6_compact ι) :
    definition_7_3_6 ι :=
  h.toIsContinuousEmbedding

end Embedding

/-! ### Theorem 7.3.1: $C^\infty(\Omega) \cap W^{k,p}(\Omega)$ is dense in $W^{k,p}(\Omega)$ -/

section Interior

variable {d : ℕ}

/-- **Theorem 7.3.1** of [han2009theoretical] (Meyers–Serrin theorem, $H = W$). Let
$\Omega \subseteq \mathbb{R}^d$ be open, let $k \ge 0$ be an integer and let $1 \le p < \infty$.
For every $v \in W^{k,p}(\Omega)$ there is a sequence $(v_n)$ of functions with
$v_n \in C^\infty(\Omega) \cap W^{k,p}(\Omega)$ for every $n$ and
$$\|v_n - v\|_{k,p,\Omega} \to 0 \qquad (n \to \infty).$$

The functions $v_n$ are smooth in the interior of $\Omega$ only, and no regularity of
$\partial\Omega$ is assumed; Theorem 7.3.2 is the sharper statement that needs it. Membership in
$W^{k,p}(\Omega)$ is `AtkinsonHan.Chapter07.definition_7_2_2`, and $\|\cdot\|_{k,p,\Omega}$ is
`sobolevNorm`, the norm of the bundled reading of Definition 7.2.2. The proof, in
`Numlib.Analysis.Sobolev.Density`, takes an exhaustion of $\Omega$ by relatively compact open
sets, a smooth partition of unity subordinate to it, and one mollifier radius for each piece. -/
theorem theorem_7_3_1 {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : definition_7_2_2 k p Ω v) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ n, ContDiffOn ℝ ∞ (w n) (Ω : Set (EuclideanSpace ℝ (Fin d)))) ∧
        (∀ n, definition_7_2_2 k p Ω (w n)) ∧
        Tendsto (fun n ↦ sobolevNorm (w n - v) k p Ω volume) atTop (𝓝 0) :=
  hv.exists_seq_contDiffOn_tendsto_sobolevNorm hp hp'

end Interior

/-! ### Theorem 7.3.4: $C_0^\infty(\mathbb{R}^d)$ is dense in $W^{k,p}(\mathbb{R}^d)$ -/

section WholeSpace

variable {d : ℕ}

/-- **Theorem 7.3.4** of [han2009theoretical]. Let $k \ge 0$ be an integer and let
$1 \le p < \infty$. For every $v \in W^{k,p}(\mathbb{R}^d)$ there is a sequence $(\varphi_n)$ in
$C_0^\infty(\mathbb{R}^d)$ with
$$\|\varphi_n - v\|_{k,p} \to 0 \qquad (n \to \infty).$$
So $C_0^\infty(\mathbb{R}^d)$ is dense in $W^{k,p}(\mathbb{R}^d)$.

The space $C_0^\infty(\mathbb{R}^d)$ is `𝓓(⊤, ℝ)`, for the whole space
`⊤ : Opens (EuclideanSpace ℝ (Fin d))`. Every test function lies in the Sobolev space by
`TestFunction.memSobolev`. The norm is `sobolevNorm`, as in Theorem 7.3.1. On the whole space no
point is near a boundary, so one mollification approximates $v$ and all its weak derivatives at
once, and multiplication by a cut-off function $\eta(x/R)$ makes the support compact at a cost
that the Leibniz rule controls. -/
theorem theorem_7_3_4 {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : definition_7_2_2 k p ⊤ v) :
    ∃ φ : ℕ → 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin d))), ℝ),
      Tendsto (fun n ↦ sobolevNorm ((φ n : EuclideanSpace ℝ (Fin d) → ℝ) - v) k p ⊤ volume)
        atTop (𝓝 0) := by
  obtain ⟨w, hw1, hw2, hw3⟩ :=
    MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm hp hp' hv
  exact ⟨fun n ↦ ⟨w n, hw1 n, hw2 n, by simp⟩, hw3⟩

end WholeSpace

/-! ### Theorem 7.3.3: $W_0^{k,p}(\Omega)$ is the closure of $C_0^\infty(\Omega)$ -/

variable {d : ℕ}

/-- **Theorem 7.3.3** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open, let
$k \ge 0$ be an integer and let $p \ge 1$. For every $v \in W_0^{k,p}(\Omega)$ there is a
sequence $(v_n)$ in $C_0^\infty(\Omega)$ with
$$\|v_n - v\|_{k,p,\Omega} \to 0 \qquad (n \to \infty).$$

Definition 7.2.9 is formalized as the closure, in the Banach space `Sobolev ℝ k p Ω volume`, of
the elements whose function agrees almost everywhere on $\Omega$ with a test function
(`AtkinsonHan.Chapter07.definition_7_2_9`). The theorem is this closure read sequentially. An
element of the space is a tuple of derivatives and not a function, so the sequence consists of
elements $u_n$ of $W^{k,p}(\Omega)$ together with test functions $\varphi_n$, with
`Sobolev.fn (u n) = φ n` almost everywhere on $\Omega$; this is the meaning of
$v_n \in C_0^\infty(\Omega)$. The weak derivatives of $u_n$ are then the classical derivatives
of $\varphi_n$, by `TestFunction.memSobolev`. -/
theorem theorem_7_3_3 {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : Sobolev ℝ k p Ω volume}
    (hv : v ∈ definition_7_2_9 k p Ω) :
    ∃ (φ : ℕ → 𝓓(Ω, ℝ)) (u : ℕ → Sobolev ℝ k p Ω volume),
      (∀ n, Sobolev.fn (u n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))] φ n) ∧
        Tendsto (fun n ↦ ‖u n - v‖) atTop (𝓝 0) := by
  rw [definition_7_2_9, SobolevZero, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe] at hv
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hv
  choose φ hφ using fun n ↦ hu n
  exact ⟨φ, u, hφ, tendsto_iff_norm_sub_tendsto_zero.1 hlim⟩

/-!
### The domain hypothesis of the section

The results below assume an extension domain where the source assumes a Lipschitz domain. The
bounded $C^1$ and $C^k$ domains of Definition 7.2.1 are extension domains.
-/

section DomainHypothesis

/-- Supporting result for the domain hypothesis of Section 7.3 of [han2009theoretical]. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set whose boundary is of class $C^1$ in
the sense of Definition 7.2.1. Then $\Omega$ is a $W^{1,q}$-extension domain for every exponent
$q \ge 1$, that is, `IsSobolevExtensionDomainAll (d + 1) Ω`.

This is Theorem 9.7 of [brezis2011functional]
(`IsSobolevExtensionDomainAll.of_isContDiffChartDomain`), through
`AtkinsonHan.Chapter07.definition_7_2_1_contDiffDomain`, which relates Definition 7.2.1 to the
graph domains of the backbone. The source states Section 7.3 for Lipschitz domains; a Lipschitz
domain is an extension domain by the theorem of Stein or Calderón, which is not formalized.

**Reading.** Bounded C1 domains admit first-order extensions at every p.
-/
theorem isSobolevExtensionDomainAll_of_definition_7_2_1
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : definition_7_2_1 {g | ContDiff ℝ 1 g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    IsSobolevExtensionDomainAll (d + 1) Ω :=
  IsSobolevExtensionDomainAll.of_isContDiffChartDomain
    ((definition_7_2_1_contDiffDomain 1 Ω).2 hΩ).isContDiffChartDomain
    (hb.closure.subset frontier_subset_closure)

end DomainHypothesis

/-! ### Theorem 7.3.2: density of $C^\infty(\overline\Omega)$ -/

section Density

/-- **Theorem 7.3.2** of [han2009theoretical], the order $k = 1$. Let
$\Omega \subseteq \mathbb{R}^d$ be a $W^{1,p}$-extension domain with $1 \le p < \infty$. For
every $v \in W^{1,p}(\Omega)$ there are functions $\varphi_n \in C_c^\infty(\mathbb{R}^d)$ and
elements $u_n \in W^{1,p}(\Omega)$ such that the function of $u_n$ equals $\varphi_n$ almost
everywhere on $\Omega$ and
$$\|u_n - v\|_{1,p,\Omega} \to 0 \qquad (n \to \infty).$$
So the restrictions to $\Omega$ of functions in $C_c^\infty(\mathbb{R}^d)$, and in particular
$C^\infty(\overline\Omega)$, are dense in $W^{1,p}(\Omega)$.

The source states the theorem for every order $k$ on a Lipschitz domain. Every order is
`AtkinsonHan.Chapter07.theorem_7_3_2_higher`. The domain hypothesis is
`IsSobolevExtensionDomain d p Ω`, which the bounded $C^1$ domains of Definition 7.2.1 satisfy
(`AtkinsonHan.Chapter07.isSobolevExtensionDomainAll_of_definition_7_2_1`). The proof is
Corollary 9.8 of [brezis2011functional]
(`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn`).

**Reading.** First-order density assumes an extension domain rather than Lipschitz boundary.
-/
theorem theorem_7_3_2 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} (hΩ : IsSobolevExtensionDomain d p Ω)
    (v : SobolevMultiIndex ℝ (stdBasis d) 1 p Ω volume) :
    ∃ (φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
      (u : ℕ → SobolevMultiIndex ℝ (stdBasis d) 1 p Ω volume),
      (∀ n, ContDiff ℝ ∞ (φ n)) ∧ (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, SobolevMultiIndex.fn (u n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))]
        φ n) ∧
      Tendsto (fun n ↦ ‖u n - v‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hφc, u, hu, hlim⟩ :=
    SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp' hΩ
      ⟨v, Submodule.mem_top⟩
  exact ⟨φ, u, hφ, hφc, hu, tendsto_iff_norm_sub_tendsto_zero.1 hlim⟩

/-- Supporting result for the domain hypothesis of Section 7.3 of [han2009theoretical]. Let
$k \ge 1$, let $p \in [1, \infty]$, and let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
open set whose boundary is of class $C^k$ in the sense of Definition 7.2.1. Then $\Omega$ is a
$W^{k,p}$-extension domain: there is a bounded linear extension operator
$W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$.

The proof is `IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain`, the higher-order
reflection of Exercise 7.3.2 in the charts of Theorem 9.7 of [brezis2011functional], through
`AtkinsonHan.Chapter07.definition_7_2_1_contDiffDomain`. A Lipschitz domain would satisfy the
hypothesis by Stein's universal extension theorem, which is not formalized.

**Reading.** Extension property is derived at a fixed positive order for bounded C^k boundaries.
-/
theorem isSobolevExtensionDomainOfOrder_of_definition_7_2_1 {k : ℕ} (hk : 1 ≤ k) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : definition_7_2_1 {g | ContDiff ℝ k g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    IsSobolevExtensionDomainOfOrder (d + 1) k p Ω :=
  IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain hk
    ((definition_7_2_1_contDiffDomain k Ω).2 hΩ).isContDiffChartDomain
    (hb.closure.subset frontier_subset_closure)

/-- **Theorem 7.3.2** of [han2009theoretical], every order. Let $k \ge 0$, let $1 \le p < \infty$,
and let $\Omega \subseteq \mathbb{R}^d$ be a $W^{k,p}$-extension domain. For every
$v \in W^{k,p}(\Omega)$ there are functions $\varphi_n \in C_c^\infty(\mathbb{R}^d)$ and
elements $u_n \in W^{k,p}(\Omega)$ such that the function of $u_n$ equals $\varphi_n$ almost
everywhere on $\Omega$ and
$$\|u_n - v\|_{k,p,\Omega} \to 0 \qquad (n \to \infty).$$

The source assumes a Lipschitz domain. The hypothesis is
`IsSobolevExtensionDomainOfOrder d k p Ω`, which the bounded $C^k$ domains of Definition 7.2.1
satisfy (`AtkinsonHan.Chapter07.isSobolevExtensionDomainOfOrder_of_definition_7_2_1`). The proof
is Corollary 9.8 of [brezis2011functional] at every order, through the extension operator of
`Numlib.Analysis.Sobolev.ExtensionHigher`. The order $k = 1$ is
`AtkinsonHan.Chapter07.theorem_7_3_2`.

**Reading.** Higher-order smooth approximation assumes an extension operator of the corresponding
order.
-/
theorem theorem_7_3_2_higher {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} (hΩ : IsSobolevExtensionDomainOfOrder d k p Ω)
    (v : SobolevMultiIndex ℝ (stdBasis d) k p Ω volume) :
    ∃ (φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
      (u : ℕ → SobolevMultiIndex ℝ (stdBasis d) k p Ω volume),
      (∀ n, ContDiff ℝ ∞ (φ n)) ∧ (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, SobolevMultiIndex.fn (u n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))]
        φ n) ∧
      Tendsto (fun n ↦ ‖u n - v‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hφc, u, hu, hlim⟩ :=
    SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order hp' hΩ v
  exact ⟨φ, u, hφ, hφc, hu, tendsto_iff_norm_sub_tendsto_zero.1 hlim⟩


end Density

/-! ### Theorem 7.3.5: the extension operator -/

section Extension

/-- **Theorem 7.3.5** of [han2009theoretical], the order $k = 1$. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set whose boundary is of class $C^1$ in
the sense of Definition 7.2.1, and let $p \in [1, \infty]$. There is a bounded linear operator
$E : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^{d+1})$ such that $Ev = v$ almost everywhere in
$\Omega$ for every $v$, and a constant $c$ with
$$\|Ev\|_{W^{1,p}(\mathbb{R}^{d+1})} \le c \, \|v\|_{W^{1,p}(\Omega)} \qquad \text{for all }
  v.$$

The source states Stein's universal extension theorem: one operator $E$, for a Lipschitz domain
or a half-space, bounded from $W^{k,p}(\Omega)$ to $W^{k,p}(\mathbb{R}^d)$ for every $k \ge 0$
and every $p \in [1, \infty]$, with $Ev$ smooth outside $\overline\Omega$. That statement is not
formalized; see the module documentation. This declaration is Theorem 9.7 of
[brezis2011functional] (`SobolevEuclidean.exists_extensionL`, reflection across $C^1$ charts):
one operator for each $p$, at the order $k = 1$, and $Ev$ is not smooth outside
$\overline\Omega$.

**Reading.** Bounded C1 first-order extension without universality across orders.
-/
theorem theorem_7_3_5 {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : definition_7_2_1 {g | ContDiff ℝ 1 g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ E : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume →L[ℝ]
        SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p ⊤ volume,
      (∀ v, SobolevMultiIndex.fn (E v)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn v) ∧
      ∃ c : ℝ, ∀ v, ‖E v‖ ≤ c * ‖v‖ := by
  have h1 : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ((definition_7_2_1_contDiffDomain 1 Ω).2 hΩ).isContDiffChartDomain
  have h2 : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hb.closure.subset frontier_subset_closure
  have h3 := SobolevEuclidean.exists_extensionL (p := p) h1 h2
  obtain ⟨E, c, hE⟩ := h3
  exact ⟨E, fun v ↦ (hE v).1, c, fun v ↦ (hE v).2.2⟩

/-- **Theorem 7.3.5** of [han2009theoretical], the order $k \ge 1$. Let $k \ge 1$, let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set whose boundary is of class $C^k$ in
the sense of Definition 7.2.1, and let $p \in [1, \infty]$. There is a bounded linear operator
$E : W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$ such that $Ev = v$ almost everywhere in
$\Omega$ for every $v$, and a constant $c$ with
$$\|Ev\|_{W^{k,p}(\mathbb{R}^{d+1})} \le c \, \|v\|_{W^{k,p}(\Omega)} \qquad \text{for all }
  v.$$

The universal operator of the source, one for all $k$ and $p$, is not formalized; see the module
documentation. The proof is the higher-order reflection of Exercise 7.3.2 in the charts of
Theorem 9.7 of [brezis2011functional] (`SobolevEuclidean.exists_extensionL_of_order`): one
operator for each $k$ and $p$, and $Ev$ is not smooth outside $\overline\Omega$. The order
$k = 1$ on a $C^1$ domain is `AtkinsonHan.Chapter07.theorem_7_3_5`.
`AtkinsonHan.Chapter07.theorem_7_3_5_order_lp` adds the $L^p$ bound, and
`AtkinsonHan.Chapter07.theorem_7_3_5_order_uniform` gives one operator for every exponent.

**Reading.** Extension at fixed positive order for a bounded C^k domain.
-/
theorem theorem_7_3_5_order {k : ℕ} (hk : 1 ≤ k) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : definition_7_2_1 {g | ContDiff ℝ k g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ E : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
        SobolevMultiIndex ℝ (stdBasis (d + 1)) k p ⊤ volume,
      (∀ v, SobolevMultiIndex.fn (E v)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn v) ∧
      ∃ c : ℝ, ∀ v, ‖E v‖ ≤ c * ‖v‖ := by
  have h1 : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ((definition_7_2_1_contDiffDomain k Ω).2 hΩ).isContDiffChartDomain
  have h2 : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hb.closure.subset frontier_subset_closure
  have h3 := SobolevEuclidean.exists_extensionL_of_order (p := p) hk h1 h2
  obtain ⟨E, c, hE⟩ := h3
  exact ⟨E, fun v ↦ (hE v).1, c, fun v ↦ (hE v).2.2⟩

/-- **Theorem 7.3.5** of [han2009theoretical], the order $k \ge 1$ with the $L^p$ bound. Let
$k \ge 1$, let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set whose boundary is of
class $C^k$ in the sense of Definition 7.2.1, and let $p \in [1, \infty]$. There is a bounded
linear operator $E : W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$ such that $Ev = v$ almost
everywhere in $\Omega$ for every $v$, and a constant $c$ with
$$\|Ev\|_{W^{k,p}(\mathbb{R}^{d+1})} \le c \, \|v\|_{W^{k,p}(\Omega)} \quad \text{and} \quad
  \|Ev\|_{L^p(\mathbb{R}^{d+1})} \le c \, \|v\|_{L^p(\Omega)} \qquad \text{for all } v.$$

This is `AtkinsonHan.Chapter07.theorem_7_3_5_order` with the second bound added. It is the part
of Stein's universal extension theorem that the reflection gives in the order: the same operator
is bounded at the orders $0$ and $k$. Every piece of the operator (the extensions by zero with
the cut-off functions, the two chart transports, and the higher-order reflection, a finite sum
of dilations) is bounded on $L^p$, and the closed graph argument that lifts the operator from
order one to order $k$ does not change it (`SobolevEuclidean.exists_extensionL_of_order`). One
operator for all $k$ is not formalized. Example 7.4.3 on a domain
(`AtkinsonHan.Chapter07.example_7_4_3`) uses this result, because it needs $\|Ev\|_{H^{d+1}}$
and $\|Ev\|_{L^2}$ bounded by $\|v\|_{H^{d+1}(\Omega)}$ and $\|v\|_{L^2(\Omega)}$ at the same
time.

**Reading.** Bounded C^k extension also controls the original function in Lp.
-/
theorem theorem_7_3_5_order_lp {k : ℕ} (hk : 1 ≤ k) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : definition_7_2_1 {g | ContDiff ℝ k g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ E : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
        SobolevMultiIndex ℝ (stdBasis (d + 1)) k p ⊤ volume,
      (∀ v, SobolevMultiIndex.fn (E v)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn v) ∧
      ∃ c : ℝ, (∀ v, ‖E v‖ ≤ c * ‖v‖) ∧
        ∀ v, eLpNorm (SobolevMultiIndex.fn (E v)) p volume ≤ ENNReal.ofReal c
          * eLpNorm (SobolevMultiIndex.fn v) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  have h1 : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ((definition_7_2_1_contDiffDomain k Ω).2 hΩ).isContDiffChartDomain
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hb.closure.subset frontier_subset_closure
  have h3 := SobolevEuclidean.exists_extensionL_of_order (p := p) hk h1 hΓ
  obtain ⟨E, C, hE⟩ := h3
  exact ⟨E, fun v ↦ (hE v).1, C, fun v ↦ (hE v).2.2, fun v ↦ (hE v).2.1⟩

/-- **Theorem 7.3.5** of [han2009theoretical], the order $k \ge 1$ with one operator for every
exponent. Let $k \ge 1$ and let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set whose
boundary is of class $C^k$ in the sense of Definition 7.2.1. There is a map $E$ on functions
$\mathbb{R}^{d+1} \to \mathbb{R}$ with the following property. For every $p \in [1, \infty]$
there are a bounded linear operator $E_p : W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$ and a
constant $c$ such that, for every $v \in W^{k,p}(\Omega)$, the function of $E_p v$ equals $E$
applied to the function of $v$ almost everywhere on $\mathbb{R}^{d+1}$, $E_p v = v$ almost
everywhere in $\Omega$, and $\|E_p v\| \le c \, \|v\|$.

So the operators $E_p$ of two exponents agree on the functions that both spaces contain, and $E$
is one operator that restricts to a bounded operator on each $W^{k,p}(\Omega)$. This is the part
of Stein's universal extension theorem that concerns the exponent;
`AtkinsonHan.Chapter07.theorem_7_3_5_order_lp` is the part that concerns the order. One operator
for every order $k$, the smoothness of $Ev$ outside $\overline\Omega$, and Lipschitz domains are
not formalized; the reflection $\sum_j a_j v(x', l_j x_N)$ has coefficients that solve a
Vandermonde system of order $k$.

The map is $E f = 1_\Omega \theta_0 f + \sum_i 1_{U_{r_i}} \theta_i \cdot (P(f \circ H_i) \circ
H_i^{-1})$, from the proof of Theorem 9.7 of [brezis2011functional] with the higher-order
reflection $P$, read on functions. It is hidden in an existential only because the atlas and the
partition of unity are existential. The proof is
`SobolevEuclidean.exists_extensionL_of_order_uniform`, whose operators also have the $L^p$ bound
of `AtkinsonHan.Chapter07.theorem_7_3_5_order_lp`.

**Reading.** One operator works across all p at fixed positive order, with no exterior smoothness
conclusion.
-/
theorem theorem_7_3_5_order_uniform {k : ℕ} (hk : 1 ≤ k)
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : definition_7_2_1 {g | ContDiff ℝ k g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ∀ (p : ℝ≥0∞) (_ : Fact (1 ≤ p)),
        ∃ (Ep : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
            SobolevMultiIndex ℝ (stdBasis (d + 1)) k p ⊤ volume) (c : ℝ),
          ∀ v, SobolevMultiIndex.fn (Ep v) =ᵐ[volume] E (SobolevMultiIndex.fn v) ∧
            SobolevMultiIndex.fn (Ep v)
              =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
              SobolevMultiIndex.fn v ∧
            ‖Ep v‖ ≤ c * ‖v‖ := by
  have h1 : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ((definition_7_2_1_contDiffDomain k Ω).2 hΩ).isContDiffChartDomain
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hb.closure.subset frontier_subset_closure
  have h3 := SobolevEuclidean.exists_extensionL_of_order_uniform hk h1 hΓ
  obtain ⟨E, hE⟩ := h3
  refine ⟨E, fun p _ ↦ ?_⟩
  have h4 := hE p
  obtain ⟨Ep, c, hEp⟩ := h4
  exact ⟨Ep, c, fun v ↦ ⟨(hEp v).1, (hEp v).2.1, (hEp v).2.2.2⟩⟩

end Extension

/-! ### Theorems 7.3.7–7.3.9: the Sobolev embeddings -/

section Embeddings

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Theorem 7.3.7(a)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded extension domain for every exponent, let $k \ge 0$ be an integer, and let
$1 \le p < \infty$ and $1 \le q < \infty$. If $k < (d+1)/p$, $p^*$ is defined by
$1/p^* = 1/p - k/(d+1)$, and $q \le p^*$, then every $v \in W^{k,p}(\Omega)$ lies in
$L^q(\Omega)$ and
$$W^{k,p}(\Omega) \hookrightarrow L^q(\Omega).$$

The source assumes a Lipschitz domain; see the module documentation. The embedding is the
inclusion `SobolevMultiIndex.toLpₗ`, and $\hookrightarrow$ is
`AtkinsonHan.Chapter07.definition_7_3_6`. For $q \le p$ the result is Hölder's inequality on the
bounded set $\Omega$. For $p < q \le p^*$ it is Corollary 9.15 of [brezis2011functional] on the
domain (`SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension`).

**Reading.** Same subcritical exponent relation for a bounded extension domain.
-/
theorem theorem_7_3_7_a {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hk : (k : ℝ) < (d + 1 : ℕ) / p) {p' : ℝ≥0}
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / (d + 1 : ℕ)) (hq : q ≤ p') :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) := by
  have hμ := (hb.measure_lt_top (μ := volume)).ne
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hN0 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  rcases le_or_gt q p with hqp | hpq
  · have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isFiniteMeasure_restrict.2 hμ
    have hqp' : (q : ℝ≥0∞) ≤ p := by exact_mod_cast hqp
    exact ⟨fun u ↦ (SobolevMultiIndex.memLp u).mono_exponent hqp',
      SobolevMultiIndex.isContinuousEmbedding_toLpₗ_of_le hμ hqp' _⟩
  · have hq0 : (0 : ℝ) < q := hp0.trans (by exact_mod_cast hpq)
    have hp'0 : (0 : ℝ) < p' := hq0.trans_le (by exact_mod_cast hq)
    have hq' : (p : ℝ)⁻¹ - k / (d + 1 : ℕ) ≤ (q : ℝ)⁻¹ := by
      rw [← hp']
      exact inv_anti₀ hq0 (by exact_mod_cast hq)
    -- `p < q ≤ p*` forces `k ≥ 1`, hence `d + 1 > p ≥ 1`
    have hN : 2 ≤ d + 1 ∨ 1 < p := by
      left
      have hpp' : (p : ℝ) < p' := hpq.trans_le (by exact_mod_cast hq)
      have hk1 : (0 : ℝ) < k := by
        by_contra hk0
        push Not at hk0
        have hk0' : (k : ℝ) = 0 := le_antisymm hk0 (Nat.cast_nonneg k)
        rw [hk0', zero_div, sub_zero] at hp'
        exact absurd (inv_inj.1 hp') hpp'.ne'
      have h1 : (1 : ℝ) < (d + 1 : ℕ) / p := lt_of_le_of_lt (by exact_mod_cast hk1) hk
      have h2 : (p : ℝ) < (d + 1 : ℕ) := by rwa [lt_div_iff₀ hp0, one_mul] at h1
      have h3 : (1 : ℝ) < (d + 1 : ℕ) := lt_of_le_of_lt (by exact_mod_cast hp1) h2
      exact_mod_cast h3
    exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension hΩ hN
      hpq.le hq'⟩

/-- **Theorem 7.3.7(b)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded extension domain for every exponent, let $k \ge 0$ be an integer, and let
$1 \le p < \infty$ and $1 \le q < \infty$, with $d \ge 1$ or $p > 1$. If $k = (d+1)/p$, then
every $v \in W^{k,p}(\Omega)$ lies in $L^q(\Omega)$ and
$$W^{k,p}(\Omega) \hookrightarrow L^q(\Omega).$$

The hypothesis "$d \ge 1$ or $p > 1$" excludes the case $d + 1 = 1 = p$, an interval and
$W^{1,1}$, for which the backbone's form of Corollary 9.15 of [brezis2011functional] is not
available; that case is Corollary 9.11 there.

**Reading.** Same finite-q critical embedding for bounded extension domains, with one-dimensional
endpoint excluded.
-/
theorem theorem_7_3_7_b {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hN : 1 ≤ d ∨ 1 < p)
    (hk : (k : ℝ) = (d + 1 : ℕ) / p) :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) := by
  have hμ := (hb.measure_lt_top (μ := volume)).ne
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hN0 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  rcases le_or_gt q p with hqp | hpq
  · have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isFiniteMeasure_restrict.2 hμ
    have hqp' : (q : ℝ≥0∞) ≤ p := by exact_mod_cast hqp
    exact ⟨fun u ↦ (SobolevMultiIndex.memLp u).mono_exponent hqp',
      SobolevMultiIndex.isContinuousEmbedding_toLpₗ_of_le hμ hqp' _⟩
  · have hq' : (p : ℝ)⁻¹ - k / (d + 1 : ℕ) ≤ (q : ℝ)⁻¹ := by
      rw [hk, div_div, mul_comm, ← div_div, div_self hN0.ne', one_div, sub_self]
      positivity
    have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
    exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension hΩ hN'
      hpq.le hq'⟩

/-- **Theorem 7.3.7(c)** of [han2009theoretical], the case that $(d+1)/p$ is not an integer. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be an extension domain for every exponent, let $k \ge 0$ be
an integer, and let $1 \le p < \infty$, with $d \ge 1$ or $p > 1$. Suppose that $k > (d+1)/p$
and that $(d+1)/p$ is not an integer, and put $j = k - [(d+1)/p] - 1$ and
$\beta = [(d+1)/p] + 1 - (d+1)/p$. There is a constant $C \ge 0$ such that every
$v \in W^{k,p}(\Omega)$ has a representative $\tilde v \in C^j(\overline\Omega)$ with
$$\sup_{x \in \Omega} \|D^i \tilde v(x)\| \le C \, \|v\|_{k,p,\Omega} \quad (i \le j), \qquad
  \|D^j \tilde v(x) - D^j \tilde v(y)\| \le C \, \|v\|_{k,p,\Omega} \, |x - y|^\beta \quad (x, y
  \in \Omega).$$
This is the embedding $W^{k,p}(\Omega) \hookrightarrow C^{j,\beta}(\overline\Omega)$, read on
the representative.

The statement does not need $\Omega$ to be bounded. $\tilde v \in C^j(\overline\Omega)$ is
`ContDiffOnClosure`: $\tilde v$ is of class $C^j$ on $\Omega$ and its derivatives of order
$\le j$ extend continuously to $\overline\Omega$. The hypothesis "$d \ge 1$ or $p > 1$" is the
backbone's. The proof is Corollary 9.15 of [brezis2011functional]
(`SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order`). The case that $(d+1)/p$ is an
integer, where the source allows every $\beta < 1$, is
`AtkinsonHan.Chapter07.theorem_7_3_7_c_integer`.

**Reading.** Noninteger Hölder estimate stated using a representative on an extension domain.
-/
theorem theorem_7_3_7_c {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω) (hN : 1 ≤ d ∨ 1 < p)
    (hk : ((d + 1 : ℕ) : ℝ) / p < k) (hint : ∀ j : ℕ, ((d + 1 : ℕ) : ℝ) / p ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
      ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        ContDiffOnClosure ℝ ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : WithTop ℕ∞) v' Ω ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        (∀ i ≤ k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ‖iteratedFDeriv ℝ i v' x‖ ≤ C * ‖v‖) ∧
        ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ∀ y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ‖iteratedFDeriv ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) v' x
              - iteratedFDeriv ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) v' y‖
            ≤ C * ‖v‖ * ‖x - y‖ ^ (⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 - ((d + 1 : ℕ) : ℝ) / p) := by
  have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
  have hs0 : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) / p := by positivity
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 := ⟨_, rfl⟩
  have hfloor : ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ < k := Nat.floor_lt hs0 |>.2 hk
  have hjcast : (j : ℝ) = k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 := by
    have hk' : k = j + ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 := by omega
    rw [hk']
    push_cast
    ring
  have hθ : (k : ℝ) - (d + 1 : ℕ) / p - j
      = ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 - ((d + 1 : ℕ) : ℝ) / p := by
    rw [hjcast]
    ring
  have hθ0 : 0 < (k : ℝ) - (d + 1 : ℕ) / p - j := by
    rw [hθ, sub_pos]
    exact Nat.lt_floor_add_one _
  have hθ1 : (k : ℝ) - (d + 1 : ℕ) / p - j < 1 := by
    have hlt : (⌊((d + 1 : ℕ) : ℝ) / p⌋₊ : ℝ) < ((d + 1 : ℕ) : ℝ) / p :=
      lt_of_le_of_ne (Nat.floor_le hs0) (Ne.symm (hint _))
    rw [hθ]
    linarith
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order
    (N := d + 1) (m := k) (k := j) hΩ hN' hθ0 hθ1
  rw [← hθ, ← hj]
  refine ⟨C, hC0, fun v ↦ ?_⟩
  obtain ⟨v', -, hv', hae, hG, G, hGc, hGeq, hGh⟩ := hC v
  refine ⟨v', ⟨hv', fun i hi ↦ ?_⟩, hae, fun i hi x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · obtain ⟨G', hG'c, hG'eq, -⟩ := hG i (by exact_mod_cast hi)
    exact ⟨G', hG'c.continuousOn, hG'eq.symm⟩
  · obtain ⟨G', -, hG'eq, hG'b⟩ := hG i hi
    rw [hG'eq hx]
    exact hG'b x
  · rw [hGeq hx, hGeq hy]
    exact hGh x y

set_option maxHeartbeats 800000 in
-- the seven destructurings of existentials (`j`, `q`, the Morrey data at exponent `q`, the
-- order-lowering operator `T`, the representative `v'`) in the typed Sobolev context at two
-- exponents cost 0.5–1 s each, 8 s in all (profiled), and the default budget of 200 000 is
-- exhausted at about 4 s; see `notes/lessons.md`, "heartbeats are per declaration".
/-- **Theorem 7.3.7(c)** of [han2009theoretical], the case that $(d+1)/p = \ell$ is an integer. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be an extension domain for every exponent, let $k \ge 0$ be
an integer, and let $1 \le p < \infty$, with $d \ge 1$ or $p > 1$. Suppose that $(d+1)/p = \ell$
is an integer with $k > \ell$, let $0 < \beta < 1$, and put $j = k - \ell - 1$. There is a
constant $C \ge 0$ such that every $v \in W^{k,p}(\Omega)$ has a representative
$\tilde v \in C^j(\overline\Omega)$ with
$$\sup_{x \in \Omega} \|D^i \tilde v(x)\| \le C \, \|v\|_{k,p,\Omega} \quad (i \le j), \qquad
  \|D^j \tilde v(x) - D^j \tilde v(y)\| \le C \, \|v\|_{k,p,\Omega} \, |x - y|^\beta \quad (x, y
  \in \Omega).$$
This is the embedding $W^{k,p}(\Omega) \hookrightarrow C^{j,\beta}(\overline\Omega)$, read on
the representative as in `AtkinsonHan.Chapter07.theorem_7_3_7_c`.

The statement does not need $\Omega$ to be bounded. The proof embeds $W^{k,p}(\Omega)$ in
$W^{j+1,q}(\Omega)$ for every $q < \infty$ (the critical case of Corollary 9.15 of
[brezis2011functional], a bounded operator by the closed graph theorem,
`SobolevEuclidean.exists_continuousLinearMap_lower_of_order`), and for
$q = (d+1)/(1 - \beta) > d + 1$ applies Morrey's theorem $W^{j+1,q}(\Omega) \hookrightarrow
C^{j,\beta}(\overline\Omega)$ (`SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order`). The
hypothesis "$d \ge 1$ or $p > 1$" is the backbone's. The case that $(d+1)/p$ is not an integer
is `AtkinsonHan.Chapter07.theorem_7_3_7_c`.

**Reading.** Integer endpoint Hölder estimate uses an extension domain and excludes the
one-dimensional p=1 case.
-/
theorem theorem_7_3_7_c_integer {k ℓ : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω) (hN : 1 ≤ d ∨ 1 < p)
    (hℓ : ((d + 1 : ℕ) : ℝ) / p = ℓ) (hk : ℓ < k) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
      ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        ContDiffOnClosure ℝ ((k - ℓ - 1 : ℕ) : WithTop ℕ∞) v' Ω ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        (∀ i ≤ k - ℓ - 1, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ‖iteratedFDeriv ℝ i v' x‖ ≤ C * ‖v‖) ∧
        ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ∀ y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ‖iteratedFDeriv ℝ (k - ℓ - 1) v' x - iteratedFDeriv ℝ (k - ℓ - 1) v' y‖
            ≤ C * ‖v‖ * ‖x - y‖ ^ β := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = ℓ + 1 + j := ⟨k - ℓ - 1, by omega⟩
  have hj' : ℓ + 1 + j - ℓ - 1 = j := by omega
  rw [hj']
  have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hd1 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hℓ0 : (0 : ℝ) < ℓ := by rw [← hℓ]; positivity
  -- the exponent `q = (d+1)/(1 − β) > d + 1`
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = ((d + 1 : ℕ) : ℝ) / (1 - β) :=
    ⟨Real.toNNReal (((d + 1 : ℕ) : ℝ) / (1 - β)),
      Real.coe_toNNReal _ (div_nonneg hd1.le (by linarith))⟩
  have hqd : ((d + 1 : ℕ) : ℝ) < q := by
    rw [hq, lt_div_iff₀ (by linarith)]
    nlinarith
  have hq1 : (1 : ℝ) ≤ q := by
    have : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    linarith
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq1⟩
  have hpq : p ≤ q := by
    have hp : (p : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
      have h1 : ((d + 1 : ℕ) : ℝ) = ℓ * p := by rw [← hℓ]; field_simp
      have h2 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (Nat.one_le_iff_ne_zero.2 (by
        rintro rfl; simp at hℓ0))
      nlinarith
    exact_mod_cast hp.trans hqd.le
  have hr : (p : ℝ)⁻¹ - ℓ / (d + 1 : ℕ) ≤ (q : ℝ)⁻¹ := by
    have h1 : (p : ℝ)⁻¹ = ℓ / (d + 1 : ℕ) := by
      rw [← hℓ]; field_simp
    rw [h1, sub_self]
    positivity
  -- the order-lowering map and Morrey's theorem at exponent `q`
  have hθ : ((j + 1 : ℕ) : ℝ) - (d + 1 : ℕ) / q - j = β := by
    rw [hq]
    push_cast
    field_simp
    ring
  have hq1' : (1 : ℝ≥0) < q := by
    have : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    exact_mod_cast this.trans_lt hqd
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order
    (N := d + 1) (m := j + 1) (k := j) (p := q) hΩ (Or.inr hq1') (by rw [hθ]; exact hβ0)
    (by rw [hθ]; exact hβ1)
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_lower_of_order (N := d + 1) ℓ j
    (p := p) (r := q) hΩ hN' hpq hr
  refine ⟨C * ‖T‖, mul_nonneg hC0 (norm_nonneg _), fun v ↦ ?_⟩
  obtain ⟨v', -, hv', hae, hG, G, hGc, hGeq, hGh⟩ := hC (T v)
  have hTv : ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
  have hCT : C * ‖T v‖ ≤ C * ‖T‖ * ‖v‖ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hTv hC0
  refine ⟨v', ⟨hv', fun i hi ↦ ?_⟩, (hT v).symm.trans hae, fun i hi x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · obtain ⟨G', hG'c, hG'eq, -⟩ := hG i (by exact_mod_cast hi)
    exact ⟨G', hG'c.continuousOn, hG'eq.symm⟩
  · obtain ⟨G', -, hG'eq, hG'b⟩ := hG i hi
    rw [hG'eq hx]
    exact (hG'b x).trans hCT
  · rw [hGeq hx, hGeq hy, ← hθ]
    refine (hGh x y).trans ?_
    gcongr


/-- **Theorem 7.3.7** of [han2009theoretical] (Sobolev embedding theorem). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded extension domain for every exponent, let
$k \ge 0$ be an integer, and let $1 \le p < \infty$. Write $1/p^* = 1/p - k/(d+1)$.

* (a) If $k < (d+1)/p$, then $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ for every
  $q \in [1, p^*]$.
* (b) If $d \ge 1$ or $p > 1$, and $k = (d+1)/p$, then
  $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ for every $q \in [1, \infty)$.
* (c) If $d \ge 1$ or $p > 1$, $k > (d+1)/p$, and $(d+1)/p$ is not an integer, then
  $W^{k,p}(\Omega) \hookrightarrow C^{k - [(d+1)/p] - 1, \beta}(\overline\Omega)$ with
  $\beta = [(d+1)/p] + 1 - (d+1)/p$, read on continuous representatives as in
  `AtkinsonHan.Chapter07.theorem_7_3_7_c`.

The source assumes a Lipschitz domain; a bounded $C^1$ domain is an extension domain for every
exponent by `AtkinsonHan.Chapter07.isSobolevExtensionDomainAll_of_definition_7_2_1`. The three
clauses are `AtkinsonHan.Chapter07.theorem_7_3_7_a`, `AtkinsonHan.Chapter07.theorem_7_3_7_b` and
`AtkinsonHan.Chapter07.theorem_7_3_7_c`. The hypothesis "$d \ge 1$ or $p > 1$" is the
backbone's. The case of (c) in which $(d+1)/p$ is an integer, with every $\beta < 1$, is
`AtkinsonHan.Chapter07.theorem_7_3_7_c_integer`.

**Reading.** Assembles the continuous embeddings for bounded extension domains.
-/
theorem theorem_7_3_7 {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], (k : ℝ) < (d + 1 : ℕ) / p →
      (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / (d + 1 : ℕ) → q ≤ p' →
      ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
          MemLp (SobolevMultiIndex.fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h)) ∧
    (1 ≤ d ∨ 1 < p → (k : ℝ) = (d + 1 : ℕ) / p → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))],
      ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
          MemLp (SobolevMultiIndex.fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h)) ∧
    (1 ≤ d ∨ 1 < p → ((d + 1 : ℕ) : ℝ) / p < k → (∀ j : ℕ, ((d + 1 : ℕ) : ℝ) / p ≠ j) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
          ContDiffOnClosure ℝ ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : WithTop ℕ∞) v' Ω ∧
          SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            v' ∧
          (∀ i ≤ k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1,
            ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
            ‖iteratedFDeriv ℝ i v' x‖ ≤ C * ‖v‖) ∧
          ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
            ∀ y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
            ‖iteratedFDeriv ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) v' x
                - iteratedFDeriv ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) v' y‖
              ≤ C * ‖v‖ * ‖x - y‖ ^ (⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 - ((d + 1 : ℕ) : ℝ) / p)) :=
  ⟨fun _ _ _ hk hp' hq ↦ theorem_7_3_7_a hΩ hb hk hp' hq,
    fun hN hk _ _ ↦ theorem_7_3_7_b hΩ hb hN hk, fun hN hk hint ↦ theorem_7_3_7_c hΩ hN hk hint⟩

/-- **Theorem 7.3.8(a)** of [han2009theoretical] (Rellich–Kondrachov theorem). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded extension domain for every exponent, let
$1 \le p < \infty$ and $1 \le q < \infty$, and let $k$ be an integer with $1 \le k < (d+1)/p$.
If $1/p^* = 1/p - k/(d+1)$ and $q < p^*$, then every $v \in W^{k,p}(\Omega)$ lies in
$L^q(\Omega)$ and
$$W^{k,p}(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega).$$

**Reading.** The source writes the condition $k < d/p$ and leaves $k \ge 1$ implicit. The
hypothesis $k \ge 1$ is needed: at $k = 0$ the clause would say $L^p(\Omega)
\hookrightarrow\hookrightarrow L^q(\Omega)$ for $q < p$, which is false.

The proof is `SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_lt`: $W^{k,p}(\Omega)
\hookrightarrow W^{1,r}(\Omega)$ for a suitable $r$, and the Rellich–Kondrachov theorem for
$W^{1,r}(\Omega)$, Theorem 9.16 of [brezis2011functional]. -/
theorem theorem_7_3_8_a {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hk1 : 1 ≤ k)
    (hk : (k : ℝ) < (d + 1 : ℕ) / p) {p' : ℝ≥0}
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / (d + 1 : ℕ)) (hq : q < p') :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6_compact
        (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_lt k hΩ
    (hb.measure_lt_top (μ := volume)).ne hk hp' hq

/-- **Theorem 7.3.8(b)** of [han2009theoretical], as printed. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded extension domain for every exponent, let
$k \ge 0$ be an integer, and let $1 \le p < \infty$ and $1 \le q < \infty$, with $d \ge 1$ or
$p > 1$. If $k = (d+1)/p$, then every $v \in W^{k,p}(\Omega)$ lies in $L^q(\Omega)$ and
$$W^{k,p}(\Omega) \hookrightarrow L^q(\Omega).$$

**Reading.** The source prints a continuous embedding in this clause of a theorem on compact
embeddings; the printed clause is the same as Theorem 7.3.7(b). This declaration states the
clause as printed. The compact embedding, which the source presumably intends, is
`AtkinsonHan.Chapter07.theorem_7_3_8_b_compact`. -/
theorem theorem_7_3_8_b {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hN : 1 ≤ d ∨ 1 < p)
    (hk : (k : ℝ) = (d + 1 : ℕ) / p) :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) :=
  theorem_7_3_7_b hΩ hb hN hk

/-- **Theorem 7.3.8(b)** of [han2009theoretical], the compact embedding. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded extension domain for every exponent with
$d \ge 1$, let $k \ge 0$ be an integer, and let $1 \le p < \infty$ and $1 \le q < \infty$. If
$k = (d+1)/p$, then every $v \in W^{k,p}(\Omega)$ lies in $L^q(\Omega)$ and
$$W^{k,p}(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega).$$

The source prints a continuous embedding; see `AtkinsonHan.Chapter07.theorem_7_3_8_b`. The
hypothesis $k = (d+1)/p$ gives $k \ge 1$. The proof is
`SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_eq`: $W^{k,p}(\Omega) \hookrightarrow
W^{1,d+1}(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega)$.

**Generalization.** Strengthens the printed critical embedding to compactness.
-/
theorem theorem_7_3_8_b_compact {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hd : 1 ≤ d)
    (hk : (k : ℝ) = (d + 1 : ℕ) / p) :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6_compact
        (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hk1 : 1 ≤ k := by
    have h1 : (0 : ℝ) < (d + 1 : ℕ) / p := div_pos (by positivity) hp0
    rw [← hk] at h1
    exact_mod_cast h1
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_eq k hΩ
    (hb.measure_lt_top (μ := volume)).ne (by omega) hk

/-- **Theorem 7.3.8(c)** of [han2009theoretical], the target $C(\overline\Omega)$. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded extension domain for every exponent, let
$k \ge 0$ be an integer, and let $1 \le p < \infty$, with $d \ge 1$ or $p > 1$. If
$k > (d+1)/p$, then there is a bounded linear map
$\iota : W^{k,p}(\Omega) \to C(\overline\Omega)$ such that, for every $v$, $\iota v$ is the
restriction to $\overline\Omega$ of a continuous function $\tilde v$ on $\mathbb{R}^{d+1}$ that
equals $v$ almost everywhere on $\Omega$, and
$$W^{k,p}(\Omega) \hookrightarrow\hookrightarrow C(\overline\Omega) \quad \text{along } \iota.$$

The source has the target $C^{k - [(d+1)/p] - 1, \beta}(\overline\Omega)$; this declaration is
the case $\beta = 0$ with the order $k - [(d+1)/p] - 1$ replaced by $0$. The Hölder target is
`AtkinsonHan.Chapter07.theorem_7_3_8_c_holder`. The space $C(\overline\Omega)$ is
`C(closure Ω, ℝ)`, with the sup norm since $\overline\Omega$ is compact. The proof is
`SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`: $W^{k,p}(\Omega)
\hookrightarrow W^{1,r}(\Omega)$ for some $r > d + 1$, and the Arzelà–Ascoli theorem. The
hypothesis "$d \ge 1$ or $p > 1$" is the backbone's.

**Reading.** Compact continuous-function target on the closure, with the extension-domain
hypotheses.
-/
theorem theorem_7_3_8_c {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hN : 1 ≤ d ∨ 1 < p)
    (hk : ((d + 1 : ℕ) : ℝ) / p < k) :
    haveI : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isCompact_iff_compactSpace.1 hb.isCompact_closure
    ∃ ι : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
        C(closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ℝ),
      (∀ v, ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        ∀ x, ι v x = v' x) ∧
      definition_7_3_6_compact ι.toLinearMap := by
  have : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hk1 : 1 ≤ k := by
    have h1 : (0 : ℝ) < (d + 1 : ℕ) / p := div_pos (by positivity) hp0
    exact_mod_cast h1.trans hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order k hΩ hN' hk
    subset_closure

/-- **Theorem 7.3.8(c)** of [han2009theoretical], the Hölder target. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded extension domain for every exponent, let
$k \ge 0$ be an integer, and let $1 \le p < \infty$, with $d \ge 1$ or $p > 1$. Suppose that
$k > (d+1)/p$, put $j = k - [(d+1)/p] - 1$, and let $0 < \beta < [(d+1)/p] + 1 - (d+1)/p$. Then
there is a bounded linear map $\iota : W^{k,p}(\Omega) \to C^{j,\beta}(\overline\Omega)$ such
that, for every $v$, $\iota v$ agrees on $\overline\Omega$ with a continuous function $\tilde v$
on $\mathbb{R}^{d+1}$ that equals $v$ almost everywhere on $\Omega$, and
$$W^{k,p}(\Omega) \hookrightarrow\hookrightarrow C^{j,\beta}(\overline\Omega) \quad \text{along
  } \iota.$$

The Hölder space is `HolderSpace` of `Numlib.Analysis.Calculus.HolderSpace`. When $(d+1)/p$ is
an integer the bound on $\beta$ reads $\beta < 1$. The proof is
`SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_lt`: the Arzelà–Ascoli theorem with
Hölder interpolation in $C^{j,\cdot}(\overline\Omega)$, together with the sharp exponent of
Corollary 9.15 of [brezis2011functional] when $(d+1)/p$ is not an integer, and the embedding
$W^{k,p}(\Omega) \hookrightarrow W^{j+1,q}(\Omega)$ with Morrey's theorem at the exponent $q$
when it is. The hypothesis "$d \ge 1$ or $p > 1$" is the backbone's. The case $\beta = 0$, with
the target $C(\overline\Omega)$, is `AtkinsonHan.Chapter07.theorem_7_3_8_c`.

**Reading.** Positive Hölder exponent case uses bounded extension domains and excludes the
one-dimensional endpoint.
-/
theorem theorem_7_3_8_c_holder {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hN : 1 ≤ d ∨ 1 < p)
    (hk : ((d + 1 : ℕ) : ℝ) / p < k) {β : ℝ≥0} (hβ0 : 0 < β)
    (hβ : (β : ℝ) < ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 - ((d + 1 : ℕ) : ℝ) / p) :
    ∃ ι : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
        HolderSpace Ω ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) β,
      (∀ v, ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        ∀ x, ι v x = v' x) ∧
      definition_7_3_6_compact ι.toLinearMap := by
  have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
  have hs0 : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) / p := by positivity
  have hfloor : ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ < k := Nat.floor_lt hs0 |>.2 hk
  have hjcast : ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : ℝ)
      = k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hlt := Nat.lt_floor_add_one (((d + 1 : ℕ) : ℝ) / p)
  have hfl := Nat.floor_le hs0
  have hm : ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : ℝ) + (d + 1 : ℕ) / p < k := by
    rw [hjcast]
    linarith
  have hle : (k : ℝ) - (d + 1 : ℕ) / p - ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : ℝ) ≤ 1 := by
    rw [hjcast]
    linarith
  have hβ' : (β : ℝ) < k - (d + 1 : ℕ) / p - ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : ℝ) := by
    rw [hjcast]
    linarith
  exact SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_lt (N := d + 1) _ hΩ hb
    (by omega) hN' hm hle hβ0 hβ'

/-- **Theorem 7.3.8** of [han2009theoretical] (compact Sobolev embedding theorem, Rellich–Kondrachov
theorem). Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded extension domain for every
exponent, let $k \ge 0$ be an integer, and let $1 \le p < \infty$. Write
$1/p^* = 1/p - k/(d+1)$.

* (a) If $1 \le k < (d+1)/p$, then $W^{k,p}(\Omega) \hookrightarrow\hookrightarrow L^q(\Omega)$
  for every $q \in [1, p^*)$.
* (b) If $d \ge 1$ or $p > 1$, and $k = (d+1)/p$, then
  $W^{k,p}(\Omega) \hookrightarrow L^q(\Omega)$ for every $q \in [1, \infty)$.
* (c) If $d \ge 1$ or $p > 1$, and $k > (d+1)/p$, then $W^{k,p}(\Omega)
  \hookrightarrow\hookrightarrow C(\overline\Omega)$ along a map that sends $v$ to a continuous
  representative, as in `AtkinsonHan.Chapter07.theorem_7_3_8_c`.

**Reading.** In (a) the source leaves $k \ge 1$ implicit, and (b) states a continuous embedding
as printed; see `AtkinsonHan.Chapter07.theorem_7_3_8_a` and
`AtkinsonHan.Chapter07.theorem_7_3_8_b`.

The three clauses are `AtkinsonHan.Chapter07.theorem_7_3_8_a`,
`AtkinsonHan.Chapter07.theorem_7_3_8_b` and `AtkinsonHan.Chapter07.theorem_7_3_8_c`. The compact
form of (b) is `AtkinsonHan.Chapter07.theorem_7_3_8_b_compact`. Clause (c) is the case
$\beta = 0$ of the target $C^{k - [(d+1)/p] - 1, \beta}(\overline\Omega)$ of the source; the
Hölder target is `AtkinsonHan.Chapter07.theorem_7_3_8_c_holder`. -/
theorem theorem_7_3_8 {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    haveI : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isCompact_iff_compactSpace.1 hb.isCompact_closure
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], 1 ≤ k → (k : ℝ) < (d + 1 : ℕ) / p →
      (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / (d + 1 : ℕ) → q < p' →
      ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
          MemLp (SobolevMultiIndex.fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        definition_7_3_6_compact
          (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h)) ∧
    (1 ≤ d ∨ 1 < p → (k : ℝ) = (d + 1 : ℕ) / p → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))],
      ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
          MemLp (SobolevMultiIndex.fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h)) ∧
    (1 ≤ d ∨ 1 < p → ((d + 1 : ℕ) : ℝ) / p < k →
      ∃ ι : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
          C(closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ℝ),
        (∀ v, ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
          SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            v' ∧
          ∀ x, ι v x = v' x) ∧
        definition_7_3_6_compact ι.toLinearMap) :=
  ⟨fun _ _ _ hk1 hk hp' hq ↦ theorem_7_3_8_a hΩ hb hk1 hk hp' hq,
    fun hN hk _ _ ↦ theorem_7_3_8_b hΩ hb hN hk, fun hN hk ↦ theorem_7_3_8_c hΩ hb hN hk⟩

/-- **Theorem 7.3.9** of [han2009theoretical], the case $p < \infty$. Let $k > l \ge 0$ be integers,
let $1 \le p < \infty$, and let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
$W^{1,p}$-extension domain. Then
$$W^{k,p}(\Omega) \hookrightarrow\hookrightarrow W^{l,p}(\Omega)$$
along the inclusion `SobolevMultiIndex.toLowerOrderL`, which forgets the derivatives of order
greater than $l$.

The source assumes a nonempty open bounded Lipschitz domain. The proof is
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt`, Theorem 9.16 of
[brezis2011functional] applied repeatedly. The case $p = \infty$ is
`AtkinsonHan.Chapter07.theorem_7_3_9_top`.

**Reading.** Compact reduction in differentiability order assumes an extension domain.
-/
theorem theorem_7_3_9 {k l : ℕ} (hlk : l < k) {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    definition_7_3_6_compact
      (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume hlk.le).toLinearMap :=
  SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt hΩ (hb.measure_lt_top (μ := volume)).ne
    hlk

/-- **Theorem 7.3.9** of [han2009theoretical], the case $p = \infty$. Let $k > l \ge 0$ be integers
and let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $W^{1,\infty}$-extension domain. Then
$$W^{k,\infty}(\Omega) \hookrightarrow\hookrightarrow W^{l,\infty}(\Omega)$$
along the inclusion `SobolevMultiIndex.toLowerOrderL`.

The source assumes a nonempty open bounded Lipschitz domain, which is a $W^{1,\infty}$-extension
domain by Stein's theorem, not formalized. The bounded $C^1$ domains of Definition 7.2.1 are
$W^{1,\infty}$-extension domains by `AtkinsonHan.Chapter07.theorem_7_3_5`. The proof is
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt`: the compact embedding
$W^{1,\infty}(\Omega) \hookrightarrow\hookrightarrow L^\infty(\Omega)$ is the Arzelà–Ascoli
theorem for the Lipschitz representatives of the extensions, and it is applied repeatedly as for
$p < \infty$. The case $1 \le p < \infty$ is `AtkinsonHan.Chapter07.theorem_7_3_9`.

**Reading.** Essentially bounded compact reduction of order assumes an extension domain.
-/
theorem theorem_7_3_9_top {k l : ℕ} (hlk : l < k) (hΩ : IsSobolevExtensionDomain (d + 1) ⊤ Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    definition_7_3_6_compact
      (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) ⊤ Ω volume hlk.le).toLinearMap :=
  SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt hΩ hb hlk

end Embeddings

/-! ### Theorem 7.3.10: the trace operator -/

section Trace

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Theorem 7.3.10(a), (b)** of [han2009theoretical] (trace theorem). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with boundary $\Gamma$ and surface
measure $\sigma$, and let $1 \le p < \infty$. The trace operator
$\gamma : W^{1,p}(\Omega) \to L^p(\Gamma)$ is linear and bounded, and

* (a) $\gamma v = v|_\Gamma$ for $v \in W^{1,p}(\Omega) \cap C(\overline\Omega)$: if a function
  $\tilde v$ that is continuous on $\overline\Omega$ equals $v$ almost everywhere on $\Omega$,
  then $\gamma v = \tilde v$ $\sigma$-almost everywhere;
* (b) there is a constant $c > 0$ with $\|\gamma v\|_{L^p(\Gamma)} \le c \,
  \|v\|_{W^{1,p}(\Omega)}$ for all $v$.

The source states the theorem without proof, for a Lipschitz domain. Here $\Omega$ is a bounded
$C^1$ domain (`IsContDiffDomain 1 Ω`, which is Definition 7.2.1 by
`AtkinsonHan.Chapter07.definition_7_2_1_contDiffDomain`), on which the surface measure
`IsContDiffDomain.boundaryMeasure` and the trace operator `IsContDiffDomain.traceL` are
constructed in `Numlib.Analysis.Sobolev.Boundary.ContDiffDomain`. The trace is Nečas's: the
divergence theorem applied to $|v|^p w$, for a vector field $w$ transversal to $\Gamma$, gives
$\int_\Gamma |v|^p \, d\sigma \le C \|v\|_{W^{1,p}}^p$ for $v \in C^1(\overline\Omega)$, and the
density of $C^\infty(\overline\Omega)$ (Theorem 7.3.2) extends $\gamma$. Clause (a) uses the
uniform approximation of a function continuous up to the boundary. Clause (c) is
`AtkinsonHan.Chapter07.theorem_7_3_10_compact`. The range $\gamma(W^{1,p}(\Omega)) = W^{1 - 1/p,
p}(\Gamma)$ and the space $H^{1/2}(\Gamma)$ with the norm (7.3.2) are not formalized; see the
module documentation.

**Reading.** Continuous trace and boundary identification on bounded C1 domains.
-/
theorem theorem_7_3_10 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume)
        (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
        ContinuousOn v' (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
        (hΩ.traceL hb p hp v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ.boundaryMeasure hb] v') ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume,
        ‖hΩ.traceL hb p hp v‖ ≤ c * ‖v‖ :=
  ⟨fun v _ hv hc ↦ hΩ.traceL_ae_eq_of_continuousOn hb p hp v hv hc, (hΩ.traceL hb p hp).bound⟩

/-- Supporting result for **Definition 7.2.9** of [han2009theoretical], the trace characterization
at $k = 1$. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain and let
$1 \le p < \infty$. For $v \in W^{1,p}(\Omega)$,
$$\gamma v = 0 \iff v \in W_0^{1,p}(\Omega),$$
where $\gamma$ is the trace of Theorem 7.3.10. So $W_0^{1,p}(\Omega)$ is the kernel of the
trace.

After Definition 7.2.9 the source describes $W_0^{k,p}(\Omega)$ as the space of the functions
$v \in W^{k,p}(\Omega)$ with $\partial^\alpha v = 0$ on $\partial\Omega$ for
$|\alpha| \le k - 1$, "the meaning of this statement being made clear later after the trace
theorems are presented". This result gives that meaning at $k = 1$. Here $W_0^{1,p}(\Omega)$ is
`SobolevEuclideanZero (d + 1) 1 p Ω`, the closure of the test functions in the multi-index
reading of $W^{1,p}(\Omega)$, on which the trace is defined; it is not identified with
`AtkinsonHan.Chapter07.definition_7_2_9 1 p Ω`, the closure in the bundled reading. The source
assumes a Lipschitz domain. The proof is `IsContDiffDomain.traceL_eq_zero_iff_mem_zero`. Test
functions vanish on $\partial\Omega$ and $\gamma$ is continuous, so
$W_0^{1,p}(\Omega) \subseteq \ker\gamma$. Conversely, if $\gamma v = 0$, Green's formula against
test functions on $\mathbb{R}^{d+1}$ (`IsContDiffDomain.green_contDiff`) shows that the
extension of $v$ by zero lies in $W^{1,p}(\mathbb{R}^{d+1})$, which characterizes
$W_0^{1,p}(\Omega)$ on a $C^1$ domain (Proposition 9.18 of [brezis2011functional]).

**Reading.** Zero-boundary space equals kernel for the bounded C1 trace.
-/
theorem theorem_7_3_10_kernel {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume) :
    hΩ.traceL hb p hp v = 0 ↔ v ∈ SobolevEuclideanZero (d + 1) 1 p Ω :=
  hΩ.traceL_eq_zero_iff_mem_zero hb p hp v

/-- **Theorem 7.3.10(c)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded $C^1$ domain with boundary $\Gamma$, and let $1 < p < \infty$. The trace operator
$\gamma : W^{1,p}(\Omega) \to L^p(\Gamma)$ of `AtkinsonHan.Chapter07.theorem_7_3_10` is compact.
Equivalently, for every bounded sequence $(v_n)$ in $W^{1,p}(\Omega)$ there are a subsequence
$(v_{n'})$ and $w \in L^p(\Gamma)$ with $\gamma v_{n'} \to w$ in $L^p(\Gamma)$.

**Correction.** The source allows $1 \le p < \infty$. At $p = 1$ the statement is false: the
trace maps $W^{1,1}(\Omega)$ onto $L^1(\Gamma)$ (Gagliardo), so it is not compact. The
hypothesis here is $1 < p < \infty$.

The source assumes a Lipschitz domain; see `AtkinsonHan.Chapter07.theorem_7_3_10`. Compactness
is `IsCompactOperator` together with the sequential form of the source. The proof
(`IsContDiffDomain.isCompactOperator_traceL`) uses Nečas's inequality in the sharp form
$$\int_\Gamma |\gamma v|^p \, d\sigma \le C \left( \|v\|_{L^p}^p + \|v\|_{L^p}^{p-1} \|\nabla
  v\|_{L^p} \right),$$
applied to the differences of a bounded sequence whose parts in $L^p(\Omega)$ converge by the
Rellich–Kondrachov theorem (Theorem 7.3.8); the traces then form a Cauchy sequence in
$L^p(\Gamma)$. -/
theorem theorem_7_3_10_compact {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    IsCompactOperator (hΩ.traceL hb p hp) ∧
      ∀ v : ℕ → SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume, (∃ M : ℝ, ∀ n, ‖v n‖ ≤ M) →
        ∃ (φ : ℕ → ℕ) (w : Lp ℝ p (hΩ.boundaryMeasure hb)), StrictMono φ ∧
          Tendsto (fun n ↦ hΩ.traceL hb p hp (v (φ n))) atTop (𝓝 w) := by
  have hK := hΩ.isCompactOperator_traceL hb p hp hp1
  refine ⟨hK, fun v ⟨M, hM⟩ ↦ ?_⟩
  obtain ⟨w, -, φ, hφ, hwφ⟩ :=
    (hK.isCompact_closure_image_closedBall M).tendsto_subseq
      (x := fun n ↦ hΩ.traceL hb p hp (v n))
      fun n ↦ subset_closure ⟨v n, mem_closedBall_zero_iff.2 (hM n), rfl⟩
  exact ⟨φ, w, hφ, hwφ⟩

/-!
### Theorem 7.3.10 on a triangulated polygon

The finite element chapters apply the trace theorem to polygonal domains, which are Lipschitz but
not $C^1$. A plane domain $\Omega \subseteq \mathbb{R}^2$ with a triangulation `𝒯 : Triangulation Ω`
(`Numlib.Geometry.Triangulation`) is a second reading of the Lipschitz domain of the source. Its
boundary carries the arclength measure of the boundary edges, `Triangulation.boundaryMeasure`, and
the outward normal, `Triangulation.outwardNormal`, both from
`Numlib.Analysis.Sobolev.Boundary.Polygon`. The trace $\gamma : W^{1,p}(\Omega) \to L^p(\Gamma)$
(`Triangulation.traceL`) is glued along the boundary edges from the traces of Theorem 7.3.10 on the
open triangles, each a bounded convex set with a transversal vector field
(`Numlib.Analysis.Sobolev.Boundary.PolygonTrace`).
-/

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Theorem 7.3.10(a), (b)** of [han2009theoretical] on a triangulated polygon. Let
$\Omega \subseteq \mathbb{R}^2$ be a plane domain with a triangulation $\mathcal{T}$, let
$\Gamma$ be its boundary with the arclength measure $\sigma$ of the boundary edges, and let
$1 \le p < \infty$. The trace operator $\gamma : W^{1,p}(\Omega) \to L^p(\Gamma)$ is linear and
bounded, and

* (a) $\gamma v = v|_\Gamma$: if a function $\tilde v$ that is continuous on $\overline\Omega$
  equals $v$ almost everywhere on $\Omega$, then $\gamma v = \tilde v$ $\sigma$-almost
  everywhere;
* (b) there is a constant $c > 0$ with $\|\gamma v\|_{L^p(\Gamma)} \le c \,
  \|v\|_{W^{1,p}(\Omega)}$ for all $v$.

The source assumes a Lipschitz domain. A triangulated polygon is the instance that the finite
element chapters use, and `AtkinsonHan.Chapter07.theorem_7_3_10` is the $C^1$ instance. Clause
(c) is `AtkinsonHan.Chapter07.theorem_7_3_10_polygon_compact`. The operator $\gamma$ is
`Triangulation.traceL`: the sum over the boundary edges of the trace on the triangle that owns
the edge, extended by zero off the edge. Clause (a) is
`Triangulation.traceL_ae_eq_of_continuousOn`, Theorem 7.3.10(a) on each triangle. For a polygon
without slits (`Triangulation.InteriorEdgesSubset`: the relative interior of every interior edge
lies in $\Omega$), $\gamma$ is by definition the trace of the trace family
`Triangulation.traceFamily` (`Triangulation.traceFamily_traceL`), which the results on polygons
in Sections 7.6, 11 and 13 use. Green's formula needs the condition without slits
(`AtkinsonHan.Chapter07.proposition_7_6_1_polygon`); clauses (a)–(c) hold for every
triangulation.

**Reading.** Separate trace and norm bound for planar triangulations.
-/
theorem theorem_7_3_10_polygon {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (∀ (v : SobolevMultiIndex ℝ (stdBasis 2) 1 p Ω volume) (v' : 𝔼₂ → ℝ),
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v' →
        ContinuousOn v' (closure (Ω : Set 𝔼₂)) →
        (𝒯.traceL p hp v : 𝔼₂ → ℝ) =ᵐ[𝒯.boundaryMeasure] v') ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis 2) 1 p Ω volume,
        ‖𝒯.traceL p hp v‖ ≤ c * ‖v‖ :=
  ⟨fun v _ hv hc ↦ Triangulation.traceL_ae_eq_of_continuousOn hp v hv hc, (𝒯.traceL p hp).bound⟩

/-- **Theorem 7.3.10(c)** of [han2009theoretical] on a triangulated polygon. Let
$\Omega \subseteq \mathbb{R}^2$ be a plane domain with a triangulation $\mathcal{T}$, and let
$1 < p < \infty$. The trace operator $\gamma : W^{1,p}(\Omega) \to L^p(\Gamma)$ of
`AtkinsonHan.Chapter07.theorem_7_3_10_polygon` is compact. Equivalently, for every bounded
sequence $(v_n)$ in $W^{1,p}(\Omega)$ there are a subsequence $(v_{n'})$ and $w \in L^p(\Gamma)$
with $\gamma v_{n'} \to w$ in $L^p(\Gamma)$.

**Correction.** The source allows $1 \le p < \infty$. At $p = 1$ the trace maps
$W^{1,1}(\Omega)$ onto $L^1(\Gamma)$, so it is not compact. The hypothesis here is
$1 < p < \infty$, as in `AtkinsonHan.Chapter07.theorem_7_3_10_compact`.

The contribution of each boundary edge is compact because the trace on a triangle is compact
(`EuclideanSpace.isCompactOperator_triangleTraceL`, Nečas's inequality with the
Rellich–Kondrachov theorem on the triangle), and a finite sum of compact operators is compact
(`Triangulation.isCompactOperator_traceL`). -/
theorem theorem_7_3_10_polygon_compact {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsCompactOperator (𝒯.traceL p hp) ∧
      ∀ v : ℕ → SobolevMultiIndex ℝ (stdBasis 2) 1 p Ω volume, (∃ M : ℝ, ∀ n, ‖v n‖ ≤ M) →
        ∃ (φ : ℕ → ℕ) (w : Lp ℝ p 𝒯.boundaryMeasure), StrictMono φ ∧
          Tendsto (fun n ↦ 𝒯.traceL p hp (v (φ n))) atTop (𝓝 w) := by
  have hK := 𝒯.isCompactOperator_traceL hp hp1
  refine ⟨hK, fun v ⟨M, hM⟩ ↦ ?_⟩
  obtain ⟨w, -, φ, hφ, hwφ⟩ :=
    (hK.isCompact_closure_image_closedBall M).tendsto_subseq
      (x := fun n ↦ 𝒯.traceL p hp (v n))
      fun n ↦ subset_closure ⟨v n, mem_closedBall_zero_iff.2 (hM n), rfl⟩
  exact ⟨φ, w, hφ, hwφ⟩

end Trace

/-! ### Theorem 7.3.11: the traces of $W^{2,p}(\Omega)$ and the normal derivative -/

section NormalTrace

open SobolevMultiIndex

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Theorem 7.3.11** of [han2009theoretical], the trace $\gamma_0$ at $s = 2$. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with boundary $\Gamma$, and let
$1 \le p < \infty$. The operator $\gamma_0 : W^{2,p}(\Omega) \to L^p(\Gamma)$ is the trace
$\gamma$ of Theorem 7.3.10 applied after the inclusion $W^{2,p}(\Omega) \hookrightarrow
W^{1,p}(\Omega)$. It is linear and bounded.

The inclusion is `SobolevMultiIndex.toLowerOrderL`, which forgets the derivatives of order two.
By `AtkinsonHan.Chapter07.theorem_7_3_11_trace₀_ae_eq`, $\gamma_0 v = v|_\Gamma$ for $v$ with a
representative continuous on $\overline\Omega$. The target is $L^p(\Gamma)$ where the source has
$W^{s - 1/p, p}(\Gamma)$; see `AtkinsonHan.Chapter07.theorem_7_3_11`.

**Reading.** Order-two input and boundary Lp target for value trace.
-/
noncomputable def theorem_7_3_11_trace₀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ] Lp ℝ p (hΩ₁.boundaryMeasure hb) :=
  hΩ₁.traceL hb p hp ∘L toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume one_le_two

/-- Supporting definition for **Theorem 7.3.11** of [han2009theoretical]. For an open
$\Omega \subseteq \mathbb{R}^{d+1}$, $p \ge 1$ and $i \in \{1, \dots, d + 1\}$, this is the
partial derivative $\partial_i : W^{2,p}(\Omega) \to W^{1,p}(\Omega)$, a bounded linear
operator, which enters the normal derivative of $W^{2,p}$ functions.

It is `SobolevMultiIndex.partialDerivL` with the orders written $2$ and $1$. That operator
writes them $k + 1$ and $k$, and a sum of operators whose types agree only up to this arithmetic
cannot be rewritten with `ContinuousLinearMap.sum_apply`. -/
noncomputable def theorem_7_3_11_partialDerivL (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) (i : Fin (d + 1)) :
    SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ]
      SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume :=
  partialDerivL ℝ (stdBasis (d + 1)) p Ω volume i

/-- Supporting definition for **Theorem 7.3.11** of [han2009theoretical]. For a bounded $C^1$ domain
$\Omega \subseteq \mathbb{R}^{d+1}$ with boundary $\Gamma$, $p \ge 1$ and
$i \in \{1, \dots, d + 1\}$, this is the bounded linear operator on $L^p(\Gamma)$ of
multiplication by the component $\nu_i$ of the outward unit normal.

It is `BoundaryData.mulNormalL` for the boundary data of the domain, with the surface measure
written `hΩ₁.boundaryMeasure hb`. The backbone writes this measure `(hΩ₁.boundaryData hb).σ`,
the same measure by `IsContDiffDomain.boundaryData_σ`. -/
noncomputable def theorem_7_3_11_mulNormalL (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (i : Fin (d + 1)) :
    Lp ℝ p (hΩ₁.boundaryMeasure hb) →L[ℝ] Lp ℝ p (hΩ₁.boundaryMeasure hb) :=
  (hΩ₁.boundaryData hb).mulNormalL p i

/-- **Theorem 7.3.11** of [han2009theoretical], the normal-derivative trace $\gamma_1$ at $s = 2$.
Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with boundary $\Gamma$ and
outward unit normal $\nu$, and let $1 \le p < \infty$. The operator
$\gamma_1 : W^{2,p}(\Omega) \to L^p(\Gamma)$ is
$$\gamma_1 v = \sum_{i=1}^{d+1} \nu_i \, \gamma(\partial_i v),$$
where $\gamma$ is the trace of Theorem 7.3.10 on $W^{1,p}(\Omega)$. It is linear and bounded.

This is the normal derivative $\partial v / \partial\nu = \sum_i (\partial v / \partial x_i)
\nu_i$ of the source, read through the trace of each first derivative
(`AtkinsonHan.Chapter07.theorem_7_3_11_partialDerivL`,
`AtkinsonHan.Chapter07.theorem_7_3_11_mulNormalL`). By
`AtkinsonHan.Chapter07.theorem_7_3_11_trace₁_ae_eq`, $\gamma_1 v = (\partial v /
\partial\nu)|_\Gamma$ for $v$ with a $C^1$ representative. At $p = 2$ it is given by the same
formula as `BoundaryData.TraceFamily.normalTrace` of `Numlib.Analysis.Sobolev.Boundary.Data`.
The target is $L^p(\Gamma)$ where the source has $W^{s - 1 - 1/p, p}(\Gamma)$; see
`AtkinsonHan.Chapter07.theorem_7_3_11`.

**Reading.** Normal trace lands in Lp and is constructed for order-two input.
-/
noncomputable def theorem_7_3_11_trace₁ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ] Lp ℝ p (hΩ₁.boundaryMeasure hb) :=
  ∑ i, theorem_7_3_11_mulNormalL p hΩ₁ hb i ∘L hΩ₁.traceL hb p hp ∘L
    theorem_7_3_11_partialDerivL p Ω i

/-- **Theorem 7.3.11** of [han2009theoretical], the property $\gamma_0 v = v|_\Gamma$. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with boundary $\Gamma$ and surface
measure $\sigma$, and let $1 \le p < \infty$. If $v \in W^{2,p}(\Omega)$ equals almost
everywhere on $\Omega$ a function $\tilde v$ that is continuous on $\overline\Omega$, then
$\gamma_0 v = \tilde v$ $\sigma$-almost everywhere.

**Generalization.** The source asks $v \in C^1(\overline\Omega)$. Continuity on
$\overline\Omega$ is what the trace needs, and it is the hypothesis here.

The operator $\gamma_0$ is `AtkinsonHan.Chapter07.theorem_7_3_11_trace₀`. The result is Theorem
7.3.10(a) for the element of $W^{1,p}(\Omega)$ under $v$. -/
theorem theorem_7_3_11_trace₀_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
    {v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v')
    (hc : ContinuousOn v' (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (theorem_7_3_11_trace₀ hp hΩ₁ hb v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[hΩ₁.boundaryMeasure hb] v' :=
  hΩ₁.traceL_ae_eq_of_continuousOn hb p hp _ hv hc

/-- Supporting result for **Theorem 7.3.11** of [han2009theoretical], the trace of a first
derivative. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with surface
measure $\sigma$, let $1 \le p < \infty$, and let $i \in \{1, \dots, d + 1\}$. If
$v \in W^{2,p}(\Omega)$ equals almost everywhere on $\Omega$ a function $\tilde v$ of class
$C^1$ on $\mathbb{R}^{d+1}$, then the trace of $\partial_i v \in W^{1,p}(\Omega)$ is
$\partial_i \tilde v$ $\sigma$-almost everywhere.

The result is Theorem 7.3.10(a) for $\partial_i v$, whose continuous representative is
$\partial_i \tilde v$ (`SobolevEuclidean.weakDeriv_singleLE_ae_eq_fderiv`).

**Reading.** Identification of partial trace uses globally C1 representatives in the order-two
setting.
-/
theorem theorem_7_3_11_traceL_partialDerivL_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
    {v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v')
    (hv' : ContDiff ℝ 1 v') (i : Fin (d + 1)) :
    (hΩ₁.traceL hb p hp (theorem_7_3_11_partialDerivL p Ω i v) :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb]
      fun x ↦ fderiv ℝ v' x (EuclideanSpace.single i 1) := by
  refine hΩ₁.traceL_ae_eq_of_continuousOn hb p hp _ ?_
    ((hv'.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
  rw [theorem_7_3_11_partialDerivL, partialDerivL_apply, fn_partialDeriv]
  exact SobolevEuclidean.weakDeriv_singleLE_ae_eq_fderiv v hv hv' i

/-- **Theorem 7.3.11** of [han2009theoretical], the property $\gamma_1 v = (\partial v /
\partial\nu)|_\Gamma$. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with
boundary $\Gamma$, surface measure $\sigma$ and outward unit normal $\nu$, and let
$1 \le p < \infty$. If $v \in W^{2,p}(\Omega)$ equals almost everywhere on $\Omega$ a function
$\tilde v$ of class $C^1$ on $\mathbb{R}^{d+1}$, then
$$\gamma_1 v = \sum_{i=1}^{d+1} \nu_i \, \frac{\partial \tilde v}{\partial x_i} \qquad
  \sigma\text{-almost everywhere on } \Gamma,$$
the classical normal derivative $\partial \tilde v / \partial\nu$ of the source.

**Reading.** The source asks $v \in W^{s,p}(\Omega) \cap C^1(\overline\Omega)$. This is read as
a representative of class $C^1$ on $\mathbb{R}^{d+1}$, whose derivative is then continuous up to
the boundary.

The operator $\gamma_1$ is `AtkinsonHan.Chapter07.theorem_7_3_11_trace₁`. The proof is termwise:
the trace of $\partial_i v$ is $\partial_i \tilde v$
(`AtkinsonHan.Chapter07.theorem_7_3_11_traceL_partialDerivL_ae_eq`), and multiplication by
$\nu_i$ acts pointwise (`BoundaryData.coeFn_mulNormalL`). -/
theorem theorem_7_3_11_trace₁_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
    {v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v')
    (hv' : ContDiff ℝ 1 v') :
    (theorem_7_3_11_trace₁ hp hΩ₁ hb v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[hΩ₁.boundaryMeasure hb]
        fun x ↦ ∑ i, hΩ₁.outwardNormal hb x i * fderiv ℝ v' x (EuclideanSpace.single i 1) := by
  rw [theorem_7_3_11_trace₁, sum_apply]
  have h2 := Lp.coeFn_finsetSum (μ := hΩ₁.boundaryMeasure hb) Finset.univ fun i ↦
    (theorem_7_3_11_mulNormalL p hΩ₁ hb i ∘L hΩ₁.traceL hb p hp ∘L
      theorem_7_3_11_partialDerivL p Ω i) v
  have h3 : ∀ i : Fin (d + 1), (theorem_7_3_11_mulNormalL p hΩ₁ hb i
      (hΩ₁.traceL hb p hp (theorem_7_3_11_partialDerivL p Ω i v)) :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb]
      fun x ↦ hΩ₁.outwardNormal hb x i * (hΩ₁.traceL hb p hp
        (theorem_7_3_11_partialDerivL p Ω i v) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x :=
    fun i ↦ (hΩ₁.boundaryData hb).coeFn_mulNormalL p i
      (hΩ₁.traceL hb p hp (theorem_7_3_11_partialDerivL p Ω i v))
  have hi := ae_all_iff.2 fun i ↦ theorem_7_3_11_traceL_partialDerivL_ae_eq hp hΩ₁ hb v hv hv' i
  filter_upwards [h2, ae_all_iff.2 h3, hi] with x hx2 hx3 hxi
  rw [hx2, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by
    change (theorem_7_3_11_mulNormalL p hΩ₁ hb i (hΩ₁.traceL hb p hp
      (theorem_7_3_11_partialDerivL p Ω i v)) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x = _
    rw [hx3 i, hxi i]

/-- **Theorem 7.3.11** of [han2009theoretical], the $L^p$ clause at $s = 2$. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^2$ domain with boundary $\Gamma$, surface
measure $\sigma$ and outward unit normal $\nu$, and let $1 \le p < \infty$. There are bounded
linear operators $\gamma_0, \gamma_1 : W^{2,p}(\Omega) \to L^p(\Gamma)$ such that

* $\gamma_0 v = \tilde v$ $\sigma$-almost everywhere whenever $v$ equals almost everywhere on
  $\Omega$ a function $\tilde v$ continuous on $\overline\Omega$;
* $\gamma_1 v = \sum_i \nu_i \, \partial \tilde v / \partial x_i$ $\sigma$-almost everywhere
  whenever $v$ equals almost everywhere on $\Omega$ a function $\tilde v$ of class $C^1$ on
  $\mathbb{R}^{d+1}$;
* every bounded linear operator $W^{2,p}(\Omega) \to L^p(\Gamma)$ with the first property is
  $\gamma_0$, and every one with the second property is $\gamma_1$.

The operators are `AtkinsonHan.Chapter07.theorem_7_3_11_trace₀` and
`AtkinsonHan.Chapter07.theorem_7_3_11_trace₁`, and the first two clauses are
`AtkinsonHan.Chapter07.theorem_7_3_11_trace₀_ae_eq` and
`AtkinsonHan.Chapter07.theorem_7_3_11_trace₁_ae_eq`. The source assumes a bounded open set with
$C^{k,1}$ boundary, $k \ge s - 1 = 1$, and has the targets $W^{s - 1/p, p}(\Gamma)$ and
$W^{s - 1 - 1/p, p}(\Gamma)$, onto which $\gamma_0$ and $\gamma_1$ are surjective. The
fractional targets, the surjectivity and general $s$ and $k$ are not formalized; see the module
documentation. Here the boundary is $C^2$ instead of $C^{1,1}$. Existence and the two formulas
hold on a bounded $C^1$ domain (`hΩ₁`, on which $\sigma$, $\nu$ and the trace of Theorem 7.3.10
are defined). The $C^2$ hypothesis `hΩ` enters only the uniqueness. That rests on the density in
$W^{2,p}(\Omega)$ of the restrictions of $C_c^\infty(\mathbb{R}^{d+1})$
(`AtkinsonHan.Chapter07.theorem_7_3_2_higher` at order 2, through the extension operator of
order two on $C^2$ chart domains, `IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain`):
both $\gamma_0$ and $\gamma_1$ are prescribed on such functions, and two continuous linear maps
that agree on a dense subspace are equal. The $C^1$ hypothesis is stated separately, although it
follows from the $C^2$ one, so that the surface measure can refer to it.

**Reading.** Unique Lp traces for order two and finite p without the higher-order Sobolev targets or
surjectivity.
-/
theorem theorem_7_3_11 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ γ₀ γ₁ : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ]
        Lp ℝ p (hΩ₁.boundaryMeasure hb),
      (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
          (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
        fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
        ContinuousOn v' (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
        (γ₀ v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb] v')
      ∧ (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
          (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
        fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
        ContDiff ℝ 1 v' →
        (γ₁ v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb]
          fun x ↦ ∑ i, hΩ₁.outwardNormal hb x i * fderiv ℝ v' x (EuclideanSpace.single i 1))
      ∧ (∀ γ₀' : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ]
            Lp ℝ p (hΩ₁.boundaryMeasure hb),
        (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
            (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
          fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
          ContinuousOn v' (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
          (γ₀' v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb] v') →
        γ₀' = γ₀)
      ∧ (∀ γ₁' : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ]
            Lp ℝ p (hΩ₁.boundaryMeasure hb),
        (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
            (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
          fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
          ContDiff ℝ 1 v' →
          (γ₁' v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb]
            fun x ↦ ∑ i, hΩ₁.outwardNormal hb x i * fderiv ℝ v' x (EuclideanSpace.single i 1)) →
        γ₁' = γ₁) := by
  -- density of the elements with a smooth compactly supported representative in `W^{2,p}(Ω)`
  have hext : IsSobolevExtensionDomainOfOrder (d + 1) 2 p Ω :=
    IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain one_le_two hΩ.isContDiffChartDomain
      (hb.closure.subset frontier_subset_closure)
  have hdense : Dense {v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume |
      ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, ContDiff ℝ ∞ v' ∧ HasCompactSupport v' ∧
        fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v'} := by
    intro v
    have h := SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order hp hext v
    obtain ⟨φ, hφ, hφc, w, hw, hwv⟩ := h
    exact mem_closure_iff_seq_limit.2 ⟨w, fun n ↦ ⟨φ n, hφ n, hφc n, hw n⟩, hwv⟩
  have hspan := hdense.mono (Submodule.subset_span (R := ℝ))
  refine ⟨theorem_7_3_11_trace₀ hp hΩ₁ hb, theorem_7_3_11_trace₁ hp hΩ₁ hb,
    fun v v' hv hc ↦ theorem_7_3_11_trace₀_ae_eq hp hΩ₁ hb v hv hc,
    fun v v' hv hv' ↦ theorem_7_3_11_trace₁_ae_eq hp hΩ₁ hb v hv hv', fun γ₀' h ↦ ?_,
    fun γ₁' h ↦ ?_⟩
  · refine ContinuousLinearMap.ext_on hspan ?_
    rintro v ⟨v', hv', -, hv⟩
    exact Lp.ext ((h v v' hv hv'.continuous.continuousOn).trans
      (theorem_7_3_11_trace₀_ae_eq hp hΩ₁ hb v hv hv'.continuous.continuousOn).symm)
  · refine ContinuousLinearMap.ext_on hspan ?_
    rintro v ⟨v', hv', -, hv⟩
    exact Lp.ext ((h v v' hv (hv'.of_le (by simp))).trans
      (theorem_7_3_11_trace₁_ae_eq hp hΩ₁ hb v hv (hv'.of_le (by simp))).symm)

end NormalTrace

/-! ### Section 7.3.5: equivalent norms (Deny–Lions) -/

section DenyLions

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Equation (7.3.3)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open,
$k \ge 0$, $p \ge 1$, and let $f_j$, $j \in J$, be finitely many seminorms on $W^{k,p}(\Omega)$.
For $v \in W^{k,p}(\Omega)$ this is the quantity
$$\|v\| = |v|_{k,p,\Omega} + \sum_{j \in J} f_j(v),$$
where $|v|_{k,p,\Omega} = \bigl(\int_\Omega \sum_{|\alpha| = k} |\partial^\alpha v|^p \,
dx\bigr)^{1/p}$.

The seminorm $|\cdot|_{k,p,\Omega}$ is `SobolevMultiIndex.topSeminorm`; its formula is
`SobolevMultiIndex.topSeminorm_eq_sum`, and at $k = 1$ it is the norm of the gradient
(`SobolevMultiIndex.topSeminorm_one_eq_gradNorm`). -/
noncomputable def equation_7_3_3 {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume) : ℝ :=
  SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) k p Ω volume v + ∑ j, f j v

/-- **Equation (7.3.4)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open,
$k \ge 0$, $1 \le p < \infty$, and let $f_j$, $j \in J$, be finitely many seminorms on
$W^{k,p}(\Omega)$. For $v \in W^{k,p}(\Omega)$ this is the quantity
$$\|v\| = \Bigl[ |v|_{k,p,\Omega}^p + \sum_{j \in J} f_j(v)^p \Bigr]^{1/p}.$$

The formula uses the real number `p.toReal`, which is $0$ at $p = \infty$. There every power
with exponent $0$ is $1$, and the quantity has the value $1$. -/
noncomputable def equation_7_3_4 {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume) : ℝ :=
  (SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) k p Ω volume v ^ p.toReal
    + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal)

/-- **Theorem 7.3.12** of [han2009theoretical] (Deny–Lions). Let $\Omega \subseteq \mathbb{R}^{d+1}$
be a connected bounded $W^{1,p}$-extension domain, let $k \ge 0$ and $1 \le p < \infty$, and let
$f_j : W^{k+1,p}(\Omega) \to \mathbb{R}$, $j \in J$, be finitely many seminorms such that

* (H1) there is a constant $c$ with $0 \le f_j(v) \le c \, \|v\|_{k+1,p,\Omega}$ for all $j$ and
  $v$;
* (H2) if $v \in \mathbb{P}_k(\Omega)$ and $f_j(v) = 0$ for all $j$, then $v = 0$.

Then each of the quantities (7.3.3), $|v|_{k+1,p,\Omega} + \sum_j f_j(v)$, and (7.3.4),
$[|v|_{k+1,p,\Omega}^p + \sum_j f_j(v)^p]^{1/p}$, vanishes only at $v = 0$, and there are
constants $c_1, c_2 > 0$ with
$$c_1 \|v\|_{k+1,p,\Omega} \le \|v\| \le c_2 \|v\|_{k+1,p,\Omega} \qquad \text{for all } v \in
  W^{k+1,p}(\Omega).$$
So both are norms on $W^{k+1,p}(\Omega)$ equivalent to $\|\cdot\|_{k+1,p,\Omega}$.

The order $k \ge 1$ of the source is written $k + 1$ here, with $k \ge 0$. The source assumes a
Lipschitz domain; the bounded $C^1$ domains are $W^{1,p}$-extension domains by
`AtkinsonHan.Chapter07.isSobolevExtensionDomainAll_of_definition_7_2_1`. $\mathbb{P}_k(\Omega)$
is read as the restrictions to $\Omega$ of the polynomials of total degree at most $k$
(`MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ k`): $v \in \mathbb{P}_k(\Omega)$ means that
the function of $v$ agrees almost everywhere on $\Omega$ with one of them. The proof is
`SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected`: the compactness
argument of the source through $W^{k+1,p}(\Omega) \hookrightarrow\hookrightarrow
W^{k,p}(\Omega)$ (Theorem 7.3.9), with the fact that $|v|_{k+1,p,\Omega} = 0$ on a connected
$\Omega$ forces $v \in \mathbb{P}_k(\Omega)$
(`SobolevMultiIndex.exists_mvPolynomial_ae_eq_of_forall_weakDeriv_eq_zero`).

**Reading.** Makes connectedness explicit and replaces a Lipschitz domain with a bounded extension
domain.
-/
theorem theorem_7_3_12 {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume))
    (h1 : ∃ c : ℝ, ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
      (∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ k, SobolevMultiIndex.fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) →
      (∀ j, f j v = 0) → v = 0) :
    ((∀ v, equation_7_3_3 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_3 f v ∧ equation_7_3_3 f v ≤ c₂ * ‖v‖) ∧
    ((∀ v, equation_7_3_4 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_4 f v ∧ equation_7_3_4 f v ≤ c₂ * ‖v‖) := by
  obtain ⟨c, hf⟩ := h1
  exact SobolevMultiIndex.norm_equiv_of_exists_norm_le_topSeminorm_add_sum (by simp) hf
    (SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected hΩ
      (hb.measure_lt_top (μ := volume)).ne hc f hf h2)

/-- **Theorem 7.3.13** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
$W^{1,p}$-extension domain, not necessarily connected, let $k \ge 0$ and $1 \le p < \infty$, and
let $f_j : W^{k+1,p}(\Omega) \to \mathbb{R}$, $j \in J$, be finitely many seminorms such that

* (H1) there is a constant $c$ with $0 \le f_j(v) \le c \, \|v\|_{k+1,p,\Omega}$ for all $j$ and
  $v$;
* (H2)′ if $|v|_{k+1,p,\Omega} = 0$ and $f_j(v) = 0$ for all $j$, then $v = 0$.

Then each of the quantities (7.3.3) and (7.3.4) vanishes only at $v = 0$, and there are
constants $c_1, c_2 > 0$ with
$$c_1 \|v\|_{k+1,p,\Omega} \le \|v\| \le c_2 \|v\|_{k+1,p,\Omega} \qquad \text{for all } v \in
  W^{k+1,p}(\Omega).$$

The source assumes an open bounded set with Lipschitz boundary. This is the form that gives the
Poincaré–Friedrichs inequality of Example 7.3.15. The proof is
`SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero`.

**Reading.** Same norm equivalence under a bounded extension-domain hypothesis.
-/
theorem theorem_7_3_13 {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume))
    (h1 : ∃ c : ℝ, ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
      SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v = 0 →
      (∀ j, f j v = 0) → v = 0) :
    ((∀ v, equation_7_3_3 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_3 f v ∧ equation_7_3_3 f v ≤ c₂ * ‖v‖) ∧
    ((∀ v, equation_7_3_4 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_4 f v ∧ equation_7_3_4 f v ≤ c₂ * ‖v‖) := by
  obtain ⟨c, hf⟩ := h1
  exact SobolevMultiIndex.norm_equiv_of_exists_norm_le_topSeminorm_add_sum (by simp) hf
    (SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero hΩ
      (hb.measure_lt_top (μ := volume)).ne f hf h2)

/-- **Theorem 7.3.14** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
$W^{1,p}$-extension domain with $\Omega = \bigcup_{\lambda \in \Lambda} \Omega_\lambda$ for
connected open sets $\Omega_\lambda$, let $k \ge 0$ and $1 \le p < \infty$, and let
$f_j : W^{k+1,p}(\Omega) \to \mathbb{R}$, $j \in J$, be finitely many seminorms such that

* (H1) there is a constant $c$ with $0 \le f_j(v) \le c \, \|v\|_{k+1,p,\Omega}$ for all $j$ and
  $v$;
* (H2) if $v|_{\Omega_\lambda} \in \mathbb{P}_k(\Omega_\lambda)$ for every $\lambda$ and
  $f_j(v) = 0$ for all $j$, then $v = 0$.

Then each of the quantities (7.3.3) and (7.3.4) vanishes only at $v = 0$, and there are
constants $c_1, c_2 > 0$ with
$$c_1 \|v\|_{k+1,p,\Omega} \le \|v\| \le c_2 \|v\|_{k+1,p,\Omega} \qquad \text{for all } v \in
  W^{k+1,p}(\Omega).$$

**Generalization.** The source takes a disjoint union of sets with Lipschitz boundaries.
Disjointness plays no role in the proof and is not assumed.

$v|_{\Omega_\lambda} \in \mathbb{P}_k(\Omega_\lambda)$ means that the function of $v$ agrees
almost everywhere on $\Omega_\lambda$ with a polynomial of total degree at most $k$. The proof
is `SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_iSup`. -/
theorem theorem_7_3_14 {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {Λ : Type*} {Ω' : Λ → Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ' : Ω = ⨆ l, Ω' l)
    (hc : ∀ l, IsPreconnected (Ω' l : Set (EuclideanSpace ℝ (Fin (d + 1))))) {J : Type*}
    [Fintype J] (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume))
    (h1 : ∃ c : ℝ, ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
      (∀ l, ∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ k, SobolevMultiIndex.fn v
        =ᵐ[volume.restrict (Ω' l : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) →
      (∀ j, f j v = 0) → v = 0) :
    ((∀ v, equation_7_3_3 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_3 f v ∧ equation_7_3_3 f v ≤ c₂ * ‖v‖) ∧
    ((∀ v, equation_7_3_4 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_4 f v ∧ equation_7_3_4 f v ≤ c₂ * ‖v‖) := by
  obtain ⟨c, hf⟩ := h1
  exact SobolevMultiIndex.norm_equiv_of_exists_norm_le_topSeminorm_add_sum (by simp) hf
    (SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_iSup hΩ
      (hb.measure_lt_top (μ := volume)).ne hΩ' hc f hf h2)

/-- **Example 7.3.15** of [han2009theoretical], the Poincaré–Friedrichs inequality (7.3.10). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set. There is a constant $c$ with
$$\|v\|_{1,\Omega} \le c \, |v|_{1,\Omega} \qquad \text{for all } v \in H_0^1(\Omega).$$
With the inequality $|v|_{1,\Omega} \le \|v\|_{1,\Omega}$
(`SobolevMultiIndex.topSeminorm_le_norm`), the seminorm $|\cdot|_{1,\Omega}$ is a norm on
$H_0^1(\Omega)$ equivalent to the norm of $H^1(\Omega)$.

The source derives the inequality from Theorem 7.3.13 with $f_1(v) = \int_\Gamma |v| \, ds$;
that route is `AtkinsonHan.Chapter07.example_7_3_15_boundary`. Here it is Poincaré's inequality
on $W_0^{1,p}(\Omega)$ (`SobolevEuclideanZero.norm_le_gradNorm`, Corollary 9.19 of
[brezis2011functional]), which needs neither regularity of $\partial\Omega$ nor compactness,
with $c = (1 + 4R^2)^{1/2}$ for $\Omega \subseteq B(0, R)$. $H_0^1(\Omega)$ is
`SobolevEuclideanZero (d + 1) 1 2 Ω`, the closure of $C_0^\infty(\Omega)$ in the multi-index
reading of Definition 7.2.2; `AtkinsonHan.Chapter07.definition_7_2_9` is the same closure in the
bundled reading `Sobolev ℝ 1 2 Ω volume`, and the two are not identified.

**Reading.** The zero-boundary inequality needs boundedness but no Lipschitz boundary.
-/
theorem example_7_3_15 (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ c : ℝ, ∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      ‖(v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 2 Ω volume)‖
        ≤ c * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 2 Ω volume
          (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 2 Ω volume) := by
  obtain ⟨R, hR0, hR⟩ := hb.subset_ball_lt 0 0
  refine ⟨(1 + (2 * R) ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal), fun v ↦ ?_⟩
  rw [SobolevMultiIndex.topSeminorm_one_eq_gradNorm]
  exact SobolevEuclideanZero.norm_le_gradNorm (by simp) hR0.le hR v

/-!
### Examples 7.3.15 (boundary clause) and 7.3.16: Poincaré–Friedrichs inequalities through the trace
-/

section PoincareFriedrichs

local notation "𝟚" => ((2 : ℝ≥0) : ℝ≥0∞)

/-- An element of $H^1(\Omega)$ that agrees almost everywhere with a polynomial of degree at most
$0$ agrees almost everywhere with a constant. -/
private theorem fn_ae_eq_const_of_degree_zero
    {v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hv : ∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0, SobolevMultiIndex.fn v
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) :
    ∃ c : ℝ, SobolevMultiIndex.fn v
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fun _ ↦ c := by
  obtain ⟨q, hq, hvq⟩ := hv
  rw [MvPolynomial.mem_restrictTotalDegree, Nat.le_zero,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
  refine ⟨q.coeff 0, hvq.trans (Eventually.of_forall fun x ↦ ?_)⟩
  change MvPolynomial.eval (fun i ↦ x i) q = q.coeff 0
  conv_lhs => rw [hq]
  rw [MvPolynomial.eval_C]

/-- If $v \in H^1(\Omega)$, on a bounded $C^1$ domain, satisfies $|v|_{1,\Omega} = 0$ and
$\int_\Gamma |\gamma v| \, d\sigma = 0$, then $v = 0$: this is (H2)′ of Theorem 7.3.13 for this
seminorm, without connectedness.

**Reading.** Coercivity kernel argument uses the trace constructed on a bounded C1 domain.
-/
private theorem eq_zero_of_topSeminorm_eq_zero_of_integral_abs_traceL_eq_zero
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hv : SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v = 0)
    (h0 : ∫ x, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x|
      ∂(hΩ.boundaryMeasure hb) = 0) : v = 0 := by
  have hγ : hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v = 0 :=
    Lp.ext ((hΩ.traceL_ae_eq_zero_of_integral_abs_eq_zero hb 𝟚 ENNReal.coe_ne_top h0).trans
      (Lp.coeFn_zero _ _ _).symm)
  refine hΩ.eq_zero_of_gradNorm_eq_zero_of_traceL_eq_zero hb 𝟚 ENNReal.coe_ne_top ?_ hγ
  rwa [← SobolevMultiIndex.topSeminorm_one_eq_gradNorm]

/-- If $U$ has positive surface measure and $v \in H^1(\Omega)$ agrees almost everywhere with a
polynomial of degree at most $0$ and has $\int_U |\gamma v| \, d\sigma = 0$, then $v = 0$: this
is (H2) of Theorem 7.3.12 for the seminorm $f_1(v) = \int_U |\gamma v| \, d\sigma$.

**Reading.** Boundary-measure argument rules out nonzero constants using the formal C1 trace.
-/
private theorem eq_zero_of_degree_zero_of_setIntegral_abs_traceL_eq_zero
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : 0 < hΩ.boundaryMeasure hb U)
    {f : Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)}
    (hf : ∀ v, f v = ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)
    (hv : ∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0, SobolevMultiIndex.fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q)
    (hfv : ∀ _ : Unit, f v = 0) : v = 0 := by
  obtain ⟨c, hvc⟩ := fn_ae_eq_const_of_degree_zero hv
  refine hΩ.eq_zero_of_traceL_integral_abs_eq_zero hb 𝟚 ENNReal.coe_ne_top hU hvc ?_
  rw [← hf]
  exact hfv ()

/-- **Example 7.3.15** of [han2009theoretical], the boundary clause. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with boundary $\Gamma$, surface
measure $\sigma$ and trace $\gamma : H^1(\Omega) \to L^2(\Gamma)$ (Theorem 7.3.10). There is a
constant $c > 0$, depending only on $\Omega$, with
$$\|v\|_{1,\Omega} \le c \left( |v|_{1,\Omega} + \int_\Gamma |\gamma v| \, d\sigma \right)
  \qquad \text{for all } v \in H^1(\Omega).$$

The source assumes a bounded Lipschitz domain; here $\Omega$ is a bounded $C^1$ domain, on which
the trace exists. This is Theorem 7.3.13 with $k + 1 = 1$, $p = 2$, one seminorm, and
$f_1(v) = \int_\Gamma |v| \, ds$. (H1) is the boundedness of the trace. (H2)′ holds without any
connectedness of $\Omega$: if $\int_\Gamma |\gamma v| \, d\sigma = 0$, then $\gamma v = 0$, so
$v \in H_0^1(\Omega)$ by the kernel theorem (`AtkinsonHan.Chapter07.theorem_7_3_10_kernel`,
`IsContDiffDomain.mem_zero_of_traceL_eq_zero`), and Poincaré's inequality on $H_0^1(\Omega)$
(`SobolevEuclideanZero.norm_le_gradNorm`) with $|v|_{1,\Omega} = 0$ gives $v = 0$. The clause
(7.3.10) on $H_0^1(\Omega)$ is `AtkinsonHan.Chapter07.example_7_3_15`, proved directly.

**Reading.** Boundary-integral norm inequality uses bounded C1 domains.
-/
theorem example_7_3_15_boundary
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      ‖v‖ ≤ c * (SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v
        + ∫ x, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x|
          ∂(hΩ.boundaryMeasure hb)) := by
  have hΩ' : IsSobolevExtensionDomain (d + 1) 𝟚 Ω :=
    IsSobolevExtensionDomain.of_isContDiffDomain hΩ (hb.closure.subset frontier_subset_closure)
  -- the seminorm `f_1(v) = ∫_Γ |γ v| dσ` and (H1)
  obtain ⟨f, hf, h1⟩ : ∃ f : Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume),
      (∀ v, f v = ∫ x in univ, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb)) ∧
      ∃ c : ℝ, ∀ v, f v ≤ c * ‖v‖ :=
    ⟨absIntegralSeminorm (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top) univ,
      fun v ↦ absIntegralSeminorm_apply _ _ v,
      exists_absIntegralSeminorm_le (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top) univ⟩
  obtain ⟨c, hc1⟩ := h1
  -- (H2)′, through Green's formula on the zero extension
  have h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v = 0 →
        (∀ _ : Unit, f v = 0) → v = 0 := by
    intro v hv hfv
    have h0 := hfv ()
    simp only [hf, Measure.restrict_univ] at h0
    exact eq_zero_of_topSeminorm_eq_zero_of_integral_abs_traceL_eq_zero hΩ hb hv h0
  have h := theorem_7_3_13 (k := 0) hΩ' hb (fun _ : Unit ↦ f) ⟨c, fun _ v ↦ hc1 v⟩ h2
  obtain ⟨⟨-, c₁, c₂, hc₁, -, hle⟩, -⟩ := h
  refine ⟨c₁⁻¹, inv_pos.2 hc₁, fun v ↦ ?_⟩
  have key := (hle v).1
  simp only [equation_7_3_3, Fintype.sum_unique, hf, Measure.restrict_univ] at key
  rw [← div_eq_inv_mul, le_div_iff₀' hc₁]
  exact key

/-- On a bounded connected $C^1$ domain, for an open $U$ that meets $\partial\Omega$, there is
$c > 0$ with $\|v\|_{1,\Omega} \le c \, (|v|_{1,\Omega} + \int_U |\gamma v| \, d\sigma)$ on
$H^1(\Omega)$: this is Theorem 7.3.12 with $k + 1 = 1$, $p = 2$ and one seminorm.

**Reading.** The partial-boundary estimate uses a fixed set and C1 trace.
-/
private theorem exists_norm_le_topSeminorm_add_setIntegral_abs_traceL
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U)
    (hne : (U ∩ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      ‖v‖ ≤ c * (SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v
        + ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
          EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb)) := by
  have hΩ' : IsSobolevExtensionDomain (d + 1) 𝟚 Ω :=
    IsSobolevExtensionDomain.of_isContDiffDomain hΩ (hb.closure.subset frontier_subset_closure)
  obtain ⟨f, hf, h1⟩ : ∃ f : Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume),
      (∀ v, f v = ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb)) ∧
      ∃ c : ℝ, ∀ v, f v ≤ c * ‖v‖ :=
    ⟨absIntegralSeminorm (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top) U,
      fun v ↦ absIntegralSeminorm_apply _ _ v,
      exists_absIntegralSeminorm_le (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top) U⟩
  obtain ⟨c, hc1⟩ := h1
  have h := theorem_7_3_12 (k := 0) hΩ' hb hc (fun _ : Unit ↦ f) ⟨c, fun _ v ↦ hc1 v⟩
    (eq_zero_of_degree_zero_of_setIntegral_abs_traceL_eq_zero hΩ hb
      (hΩ.boundaryMeasure_pos_of_isOpen hb hU hne) hf)
  obtain ⟨⟨-, c₁, c₂, hc₁, -, hle⟩, -⟩ := h
  refine ⟨c₁⁻¹, inv_pos.2 hc₁, fun v ↦ ?_⟩
  have key := (hle v).1
  simp only [equation_7_3_3, Fintype.sum_unique, hf] at key
  rw [← div_eq_inv_mul, le_div_iff₀' hc₁]
  exact key

/-- **Example 7.3.16** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
connected $C^1$ domain with boundary $\Gamma$, surface measure $\sigma$ and trace
$\gamma : H^1(\Omega) \to L^2(\Gamma)$ (Theorem 7.3.10), and let $\Gamma_0 = U \cap \Gamma$ for
an open set $U \subseteq \mathbb{R}^{d+1}$ that meets $\Gamma$. There is a constant $c > 0$ with
$$\|v\|_{1,\Omega} \le c \left( |v|_{1,\Omega} + \int_U |\gamma v| \, d\sigma \right) \qquad
  \text{for all } v \in H^1(\Omega),$$
and therefore $\|v\|_{1,\Omega} \le c \, |v|_{1,\Omega}$ for every $v \in H^1(\Omega)$ with
$\gamma v = 0$ $\sigma$-almost everywhere on $U$. This is the Poincaré–Friedrichs inequality on
$H^1_{\Gamma_0}(\Omega) = \{v \in H^1(\Omega) : v = 0 \text{ a.e. on } \Gamma_0\}$, for a mixed
boundary condition.

**Reading.** The source takes an open nonempty subset $\Gamma_0$ of $\Gamma$. Here
$\Gamma_0 = U \cap \Gamma$, and every relatively open subset of $\Gamma$ has this form. The
condition "$v = 0$ a.e. on $\Gamma_0$" is read as $\gamma v = 0$ $\sigma$-almost everywhere on
$U$, and $\|v\|_{L^1(\Gamma_0)}$ as $\int_U |\gamma v| \, d\sigma$.

The source assumes a Lipschitz domain; see `AtkinsonHan.Chapter07.theorem_7_3_10`. The constant
depends only on $\Omega$ and $\Gamma_0$. The inequality is Theorem 7.3.12 with $k + 1 = 1$,
$p = 2$, one seminorm, and $f_1(v) = \int_{\Gamma_0} |v| \, ds$. (H1) is the boundedness of the
trace. (H2) holds because the trace of a constant is that constant (Theorem 7.3.10(a)) and
$\sigma(\Gamma_0) > 0$ (`IsContDiffDomain.boundaryMeasure_pos_of_isOpen`). -/
theorem example_7_3_16
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U)
    (hne : (U ∩ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).Nonempty) :
    ∃ c : ℝ, 0 < c ∧
      (∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
        ‖v‖ ≤ c * (SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v
          + ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
            EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb))) ∧
      ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
        (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
          =ᵐ[(hΩ.boundaryMeasure hb).restrict U] 0 →
        ‖v‖ ≤ c * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v := by
  obtain ⟨c, hc0, key⟩ :=
    exists_norm_le_topSeminorm_add_setIntegral_abs_traceL hΩ hb hc hU hne
  refine ⟨c, hc0, key, fun v hv ↦ ?_⟩
  have h0 : ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
      EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hv] with x hx
    rw [hx, Pi.zero_apply, abs_zero]
  have hv' := key v
  simp only [h0, add_zero] at hv'
  exact hv'

end PoincareFriedrichs


/-! ### Section 7.3.6: the Sobolev quotient space -/

section Quotient

/-- **Theorem 7.3.17** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
connected bounded $W^{1,p}$-extension domain, let $1 \le p < \infty$ and $k \ge 0$, and let
$V = W^{k+1,p}(\Omega)/\mathbb{P}_k(\Omega)$ with the quotient norm $\|[v]\|_V = \inf_{q \in
\mathbb{P}_k(\Omega)} \|v + q\|_{k+1,p,\Omega}$. Then:

* $|v + q|_{k+1,p,\Omega} = |v|_{k+1,p,\Omega}$ for all $v$ and all
  $q \in \mathbb{P}_k(\Omega)$, so $|\cdot|_{k+1,p,\Omega}$ is well defined on $V$;
* $|v|_{k+1,p,\Omega} = 0$ if and only if $v \in \mathbb{P}_k(\Omega)$, that is, if and only if
  $[v] = 0$;
* there are constants $c_1, c_2 > 0$ with
$$c_1 |v|_{k+1,p,\Omega} \le \|[v]\|_V \le c_2 |v|_{k+1,p,\Omega} \qquad \text{for all } v \in
  W^{k+1,p}(\Omega).$$

So $|\cdot|_{k+1,p,\Omega}$ is a norm on $V$ equivalent to $\|\cdot\|_V$. The second inequality
is (7.3.13).

The source assumes a Lipschitz domain. $\mathbb{P}_k(\Omega)$ is
`SobolevEuclidean.polynomialSubmodule`, the subspace of the elements of $W^{k+1,p}(\Omega)$
whose function agrees almost everywhere on $\Omega$ with a polynomial of total degree at most
$k$ (`SobolevEuclidean.mem_polynomialSubmodule_iff`). The quotient norm is written on
representatives, as the infimum over this subspace. The proof is the first proof of the source.
The coordinate functionals of a basis of $\mathbb{P}_k(\Omega)$ extend by the Hahn–Banach
theorem to bounded functionals $f_i$ on $W^{k+1,p}(\Omega)$, the seminorms $|f_i|$ satisfy the
hypotheses of Theorem 7.3.12, and the representative $v + q$ with $f_i(v + q) = 0$ for all $i$
gives (7.3.13) (`SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm`). The first
inequality holds with $c_1 = 1$, because $|\cdot|_{k+1,p,\Omega}$ vanishes on
$\mathbb{P}_k(\Omega)$ and is bounded by the norm.

**Reading.** Quotient norm equivalence uses bounded connected extension domain.
-/
theorem theorem_7_3_17 {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume)
        (q : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume),
        q ∈ SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb →
        SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume (v + q)
          = SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v) ∧
    (∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
        SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v = 0 ↔
          v ∈ SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
        c₁ * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v
          ≤ ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb, ‖v + q‖ ∧
        ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb, ‖v + q‖
          ≤ c₂ * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v := by
  have h := SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm (k := k) hΩ hb hc
  obtain ⟨C, hC, hle⟩ := h
  refine ⟨fun v q hq ↦ ?_, fun v ↦ ?_, 1, C, one_pos, hC, fun v ↦ ⟨?_, hle v⟩⟩
  · exact SobolevEuclidean.topSeminorm_add_of_mem_polynomialSubmodule hb v hq
  · exact SobolevEuclidean.topSeminorm_eq_zero_iff_mem_polynomialSubmodule hb hc
  · exact (one_mul _).trans_le (SobolevEuclidean.topSeminorm_le_ciInf_norm_add hb v)

/-- **Corollary 7.3.18** of [han2009theoretical], the inequality (7.3.16). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a connected bounded $H^1$-extension domain and let
$k \ge 0$. There is a constant $c$, depending only on $\Omega$ and $k$, with
$$\inf_{q \in \mathbb{P}_k(\Omega)} \|v + q\|_{k+1,\Omega} \le c \, |v|_{k+1,\Omega} \qquad
  \text{for all } v \in H^{k+1}(\Omega).$$

This is `AtkinsonHan.Chapter07.theorem_7_3_17` at $p = 2$, the form that Chapter 10 uses for the
error of finite element interpolation. The exponent is written `((2 : ℝ≥0) : ℝ≥0∞)`, the
backbone's form of $p = 2$, and $H^{k+1}(\Omega)$ is `SobolevMultiIndex ℝ (stdBasis (d + 1))
(k + 1) 2 Ω volume`.

**Reading.** The polynomial approximation bound assumes boundedness, connectedness and an extension
domain.
-/
theorem corollary_7_3_18 (hΩ : IsSobolevExtensionDomain (d + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ c : ℝ, ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω volume,
      ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := ((2 : ℝ≥0) : ℝ≥0∞)) hb, ‖v + q‖
        ≤ c * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω
          volume v := by
  have h := SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm (k := k) (p := 2) hΩ hb hc
  obtain ⟨C, -, hle⟩ := h
  exact ⟨C, hle⟩

end Quotient

end DenyLions

end AtkinsonHan.Chapter07
