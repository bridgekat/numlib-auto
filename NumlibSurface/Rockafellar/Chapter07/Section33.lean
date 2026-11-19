/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Process.Duality
import Numlib.Analysis.Convex.Saddle.Conjugate
import NumlibSurface.Rockafellar.Chapter06.Section30

/-!
# Rockafellar, Section 33: Saddle-functions

This module formalizes Section 33 of [rockafellar1970convex] (pp. 349–358): concave-convex functions
$K$ on $\mathbb{R}^m \times \mathbb{R}^n$, the two partial closures $\operatorname{cl}_1 K$ and
$\operatorname{cl}_2 K$, and the correspondence between saddle-functions and convex bifunctions from
$\mathbb{R}^m$ to $\mathbb{R}^n$, which the book places "at the heart of the theory of
saddle-functions". A convex bifunction $F$ gives the saddle-function
$$K(u, x^*) = \langle Fu, x^* \rangle = \sup_x \{\langle x, x^* \rangle - (Fu)(x)\},$$
and a saddle-function $K$ gives the bifunction $Fu = K(u, \cdot)^*$. The two constructions are
inverse to each other on suitable closed classes (Theorem 33.1 and Corollary 33.1.2, Theorem 33.3
and Corollary 33.3.2). Theorem 33.2 relates $\langle Fu, x^* \rangle$ to the bracket
$\langle u, F^* x^* \rangle$ of the adjoint bifunction. The proofs specialize the backbone modules
`Numlib.Analysis.Convex.Saddle.Correspondence` and `Numlib.Analysis.Convex.Saddle.Conjugate`.

## Coverage

All 11 numbered results of Section 33 are formalized: Theorems 33.1–33.3 and Corollaries 33.1.1,
33.1.2, 33.1.3, 33.2.1, 33.2.2, 33.3.1, 33.3.2 and 33.3.3.

## Main definitions

* Section 33, `Rockafellar.cl₂`, `Rockafellar.cl₁`: the convex closure $\operatorname{cl}_2 K$ in
  the second argument and the concave closure $\operatorname{cl}_1 K$ in the first argument.
* Section 33, `Rockafellar.convexConjBracket`, `Rockafellar.concaveConjBracket`,
  `Rockafellar.bifunBracket`, `Rockafellar.concaveBifunBracket`, `Rockafellar.adjointBracket`: the
  book's notation $\langle \cdot, \cdot \rangle$ for conjugates, with one name for each meaning; the
  conjugate of a convex function, of a concave function, and the brackets of a convex bifunction, of
  a concave bifunction and of an adjoint bifunction.
* Section 33, `Rockafellar.bifunOfSaddleFn`: the convex bifunction $Fu = K(u, \cdot)^*$ of a
  saddle-function $K$.

## Main results

* Theorem 33.1, `Rockafellar.theorem_33_1_concaveConvex`, `Rockafellar.theorem_33_1_convexClosed`,
  `Rockafellar.theorem_33_1_inversion`, `Rockafellar.theorem_33_1_convexBifun`,
  `Rockafellar.theorem_33_1_imageClosed`, `Rockafellar.theorem_33_1_bracket_eq`: for a convex
  bifunction $F$, $\langle Fu, x^* \rangle$ is a convex-closed concave-convex function from which
  $\operatorname{cl}(Fu)$ is recovered; for a concave-convex $K$, $Fu = K(u, \cdot)^*$ is an
  image-closed convex bifunction with $\langle Fu, x^* \rangle = \operatorname{cl}_2 K(u, x^*)$.
* Corollary 33.1.1, `Rockafellar.corollary_33_1_1_cl₁_concaveConvex`,
  `Rockafellar.corollary_33_1_1_cl₂_concaveConvex`,
  `Rockafellar.corollary_33_1_1_cl₁_concaveClosed`, `Rockafellar.corollary_33_1_1_cl₂_convexClosed`:
  $\operatorname{cl}_1 K$ and $\operatorname{cl}_2 K$ are concave-convex, and each is closed in the
  argument that it closes.
* Corollary 33.1.2, `Rockafellar.corollary_33_1_2`: the relations
  $K(u, x^*) = \langle Fu, x^* \rangle$ and $Fu = K(u, \cdot)^*$ are a one-to-one correspondence
  between the image-closed convex bifunctions and the convex-closed concave-convex functions.
* Corollary 33.1.3, `Rockafellar.corollary_33_1_3_convex`, `Rockafellar.corollary_33_1_3_concave`,
  `Rockafellar.corollary_33_1_3_inversion`: for a polyhedral convex bifunction,
  $\langle Fu, x^* \rangle$ is polyhedral in each argument, and a proper $F$ is recovered with no
  closure.
* Theorem 33.2, `Rockafellar.theorem_33_2_first`, `Rockafellar.theorem_33_2_second`: $\langle u, F^*
  x^* \rangle = \operatorname{cl}_1 \langle Fu, x^* \rangle$ and $\operatorname{cl}_2 \langle u, F^*
  x^* \rangle = \langle (\operatorname{cl} F) u, x^* \rangle$.
* Corollary 33.2.1, `Rockafellar.corollary_33_2_1_primal`, `Rockafellar.corollary_33_2_1_dual`:
  $\langle Fu, x^* \rangle = \langle u, F^* x^* \rangle$ for
  $u \in \operatorname{ri}(\operatorname{dom} F)$, and for closed $F$ and $x^* \in
  \operatorname{ri}(\operatorname{dom} F^*)$.
* Corollary 33.2.2, `Rockafellar.corollary_33_2_2`, `Rockafellar.corollary_33_2_2_exceptional`: for
  a proper polyhedral convex $F$, $\langle Fu, x^* \rangle = \langle u, F^* x^* \rangle$ unless
  $u \notin \operatorname{dom} F$ and $x^* \notin \operatorname{dom} F^*$, in which case the two
  values are $-\infty$ and $+\infty$.
* Theorem 33.3, `Rockafellar.theorem_33_3`, `Rockafellar.theorem_33_3_lowerClosed`: the same
  relations are a one-to-one correspondence between the closed convex bifunctions and the lower
  closed concave-convex functions.
* Corollary 33.3.1, `Rockafellar.corollary_33_3_1`: a closed convex bifunction $F$ with
  $\underline{K}(u, x^*) = \langle Fu, x^* \rangle$ and $\overline{K}(u, x^*) = \langle u, F^* x^*
  \rangle$ exists, and is unique, if and only if $\operatorname{cl}_1 \underline{K} = \overline{K}$
  and $\operatorname{cl}_2 \overline{K} = \underline{K}$.
* Corollary 33.3.2, `Rockafellar.corollary_33_3_2`: $\overline{K} = \operatorname{cl}_1
  \underline{K}$ and $\underline{K} = \operatorname{cl}_2 \overline{K}$ are a one-to-one
  correspondence between the lower closed and the upper closed concave-convex functions.
* Corollary 33.3.3, `Rockafellar.corollary_33_3_3` and the declarations after it: for a finite
  continuous saddle-function $K$ on $C \times D$, there is a unique closed convex bifunction whose
  two brackets are the lower and the upper simple extensions of $K$, with
  $\operatorname{dom} F = C$, $\operatorname{dom} F^* = D$ and explicit formulas for $F$ and $F^*$.
* Section 33, `Rockafellar.fullyClosed_iff_lowerClosed_and_upperClosed`,
  `Rockafellar.convexConcave_lowerClosed_iff`, `Rockafellar.convexConcave_upperClosed_iff`,
  `Rockafellar.fullyClosedFn_of_finite`: the relations between the closedness notions, and the
  translation for convex-concave functions.

## Conventions

* A concave-convex function $K(u, v)$ is concave in the first argument and convex in the second. The
  two closures are named after the argument that they close, not after the way in which they close
  it: $\operatorname{cl}_1$ closes the first (concave) argument concavely, and $\operatorname{cl}_2$
  closes the second (convex) argument convexly. So $K$ is **lower closed** when
  $\operatorname{cl}_2 \operatorname{cl}_1 K = K$ and **upper closed** when
  $\operatorname{cl}_1 \operatorname{cl}_2 K = K$. If this orientation is reversed, every statement
  of Sections 34–37 changes. A convex-concave function is reduced to this case by negation; see
  `Rockafellar.convexConcave_lowerClosed_iff`.
* A bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ is `ConvexAnalysis.Bifun (Rn m) (Rn n)`, a
  map from $\mathbb{R}^m$ to the functions $\mathbb{R}^n \to [-\infty, +\infty]$. Its adjoint $F^*$
  is `Rockafellar.dualProgram F`.
* The brackets of bifunctions are functions of the pair $(u, x^*)$, the form in which the closedness
  predicates are stated.

## Deviations from the source

* **Theorem 33.1 and Corollary 33.1.1**, closedness (generalization). Partial
  conjugates and partial closures have the indicated closedness even for arbitrary inputs.
* **Corollary 33.2.2**, exceptional case (generalization). The two opposite infinite
  bracket values need only the stated failures of domain membership.
* **Section 33, full closedness** (generalization). The characterization by both lower
  and upper closedness holds for arbitrary functions.
* **Corollary 33.3.1** (generalization). Only the lower function needs an explicit
  concave-convex hypothesis for the representation. Its concave closure gives the upper
  function. The identities alone give the separate closedness and order conclusions.
* **Corollary 33.3.3** (generalization). The book assumes that $K$ is finite and continuous on
  $C \times D$, jointly. The statements here assume only that each section $K(u, \cdot)$ and
  $K(\cdot, x^*)$ is continuous on its set. The separate lower and upper closedness
  statements do not need sectional convexity or concavity. See `Rockafellar.corollary_33_3_3`.
-/

open Set

namespace Rockafellar

open ConvexAnalysis

/-! ### The two partial closures -/

/-- **Section 33** of [rockafellar1970convex], definition of $\operatorname{cl}_2$. For $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the **convex closure**
$\operatorname{cl}_2 K$ (the book also writes $\operatorname{cl}_v K$) is obtained by taking,
for each fixed $u$, the closure of the convex function $K(u, \cdot)$:
$$(\operatorname{cl}_2 K)(u, v) = \operatorname{cl}(K(u, \cdot))(v).$$

This is an `abbrev` for the backbone `ConvexAnalysis.partialCl₂`, with the closure
`ConvexAnalysis.convexCl`. -/
noncomputable abbrev cl₂ {m n : ℕ} (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  partialCl₂ K

/-- **Section 33** of [rockafellar1970convex], definition of $\operatorname{cl}_1$. For $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the **concave closure**
$\operatorname{cl}_1 K$ (the book also writes $\operatorname{cl}_u K$) is obtained by taking,
for each fixed $v$, the concave closure of $K(\cdot, v)$:
$$(\operatorname{cl}_1 K)(u, v) = \operatorname{cl}(K(\cdot, v))(u).$$

This is an `abbrev` for the backbone `ConvexAnalysis.partialCl₁`, with the concave closure
`ConvexAnalysis.concaveCl`. It is $\operatorname{cl}_2$ conjugated by negation, not
$\operatorname{cl}_2$ with the arguments exchanged. -/
noncomputable abbrev cl₁ {m n : ℕ} (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  partialCl₁ K

/-! ### The three brackets -/

section Brackets

variable {m n : ℕ}

/-- **Section 33** of [rockafellar1970convex], bracket of a convex function. For a convex
$f : \mathbb{R}^n \to [-\infty, +\infty]$, the book writes the conjugate as an inner product:
$$\langle f, x^* \rangle = f^*(x^*) = \sup_x \{\langle x, x^* \rangle - f(x)\}.$$
-/
noncomputable abbrev convexConjBracket (f : Rn n → EReal) : Rn n → EReal := convexConj (pairing n) f

/-- **Section 33** of [rockafellar1970convex], bracket of a concave function. For a concave
$f : \mathbb{R}^n \to [-\infty, +\infty]$, $\langle f, x^* \rangle$ is the concave conjugate
$$f^*(x^*) = \inf_x \{\langle x, x^* \rangle - f(x)\}.$$
-/
noncomputable abbrev concaveConjBracket (f : Rn n → EReal) : Rn n → EReal :=
  concaveConj (pairing n) f

/-- **Section 33** of [rockafellar1970convex], bracket of a convex bifunction. For a bifunction $F$
from $\mathbb{R}^m$ to $\mathbb{R}^n$, this is the function of the pair
$(u, x^*) \in \mathbb{R}^m \times \mathbb{R}^n$
$$\langle Fu, x^* \rangle = (Fu)^*(x^*) = \sup_x \{\langle x, x^* \rangle - (Fu)(x)\}.$$
It is the function $\underline{K}$ of Corollary 33.3.1. -/
noncomputable abbrev bifunBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  saddleOfBifun (pairing n) F

/-- **Section 33** of [rockafellar1970convex], bracket of a concave bifunction. For a bifunction $G$
from $\mathbb{R}^n$ to $\mathbb{R}^m$, this is the function of the pair
$(u, x^*) \in \mathbb{R}^m \times \mathbb{R}^n$
$$\langle u, G x^* \rangle = (G x^*)^*(u) = \inf_v \{\langle u, v \rangle - (G x^*)(v)\},$$
the concave conjugate of $G x^*$ evaluated at $u$. -/
noncomputable abbrev concaveBifunBracket (G : Bifun (Rn n) (Rn m)) : Rn m × Rn n → EReal :=
  fun p => concaveBracket (pairing m) G p.1 p.2

/-- **Section 33** of [rockafellar1970convex], bracket of the adjoint bifunction. For a bifunction
$F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, this is the function $\langle u, F^* x^* \rangle$ of
$(u, x^*)$: the concave bracket of the adjoint $F^*$ of Section 30 (`Rockafellar.dualProgram`).
It is the function $\overline{K}$ of Corollary 33.3.1. -/
noncomputable abbrev adjointBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  concaveBifunBracket (dualProgram F)

/-- **Section 33** of [rockafellar1970convex], the bifunction of a saddle-function. For $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, this is the bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$ with $Fu = K(u, \cdot)^*$:
$$(Fu)(x) = \sup_{x^*} \{\langle x, x^* \rangle - K(u, x^*)\}.$$
It is the inverse map of Corollaries 33.1.2 and 33.3.2. -/
noncomputable abbrev bifunOfSaddleFn (K : Rn m × Rn n → EReal) : Bifun (Rn m) (Rn n) :=
  bifunOfSaddle (pairing n) K

/-- For a bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, $\langle Fu, x^* \rangle = \sup_x
\{\langle x, x^* \rangle - (Fu)(x)\}$. This is the defining formula of the book. -/
theorem bifunBracket_apply (F : Bifun (Rn m) (Rn n)) (p : Rn m × Rn n) :
    bifunBracket F p = ⨆ x : Rn n, ((pairing n x p.2 : ℝ) : EReal) - F p.1 x := rfl

/-- For a bifunction $G$ from $\mathbb{R}^n$ to $\mathbb{R}^m$, $\langle u, G x^* \rangle = \inf_v
\{\langle u, v \rangle - (G x^*)(v)\}$. This is the defining formula of the book. -/
theorem concaveBifunBracket_apply (G : Bifun (Rn n) (Rn m)) (p : Rn m × Rn n) :
    concaveBifunBracket G p = ⨅ v : Rn m, ((pairing m p.1 v : ℝ) : EReal) - G p.2 v := rfl

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the bifunction $F$ with
$Fu = K(u, \cdot)^*$ satisfies $(Fu)(x) = \sup_{x^*} \{\langle x, x^* \rangle - K(u, x^*)\}$. -/
theorem bifunOfSaddleFn_apply (K : Rn m × Rn n → EReal) (u : Rn m) (x : Rn n) :
    bifunOfSaddleFn K u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - K (u, y) := rfl

/-- For $x, x^* \in \mathbb{R}^n$, the conjugate of the indicator function $\delta(\cdot \mid x)$ of
the point $x$ is $\langle \delta(\cdot \mid x), x^* \rangle = \langle x, x^* \rangle$. So the
bracket notation extends the inner product along the embedding of $\mathbb{R}^n$ into the convex
functions. -/
theorem convexConjBracket_indicatorFn (x y : Rn n) :
    convexConjBracket (indicatorFn ({x} : Set (Rn n))) y = ((pairing n x y : ℝ) : EReal) :=
  congrFun ((supportFn_eq_convexConj_indicatorFn (pairing n) {x}).symm.trans
    (supportFn_singleton (pairing n) x)) y

end Brackets

/-! ### Theorem 33.1 -/

section Thm331

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 33.1** of [rockafellar1970convex], concave-convexity. Let $F$ be a convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $K(u, x^*) = \langle Fu, x^* \rangle$ is a
concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$.

Concavity in $u$ is Theorem 5.7, for the image of the graph function of $F$. -/
theorem theorem_33_1_concaveConvex (hF : ConvexBifun F) : ConcaveConvexFn (bifunBracket F) :=
  concaveConvexFn_bracket hF (pairing n)

/-- **Theorem 33.1** of [rockafellar1970convex], convex-closedness. For every bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$, the function $\langle Fu, x^* \rangle$ is convex-closed: for
each $u$, the function $\langle Fu, \cdot \rangle$ is closed.

No hypothesis on $F$ is needed, because each $\langle Fu, \cdot \rangle$ is a conjugate.

**Reading.** Each slice is a closed conjugate for any bifunction.
-/
theorem theorem_33_1_convexClosed (F : Bifun (Rn m) (Rn n)) : PartialClosed₂ (bifunBracket F) :=
  partialClosed₂_saddleOfBifun

/-- **Theorem 33.1** of [rockafellar1970convex], inversion formula. Let $F$ be a convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then for all $u \in \mathbb{R}^m$ and
$x \in \mathbb{R}^n$,
$$(\operatorname{cl}(Fu))(x) = \sup_{x^*} \{\langle x, x^* \rangle - \langle Fu, x^*
  \rangle\}.$$

This is the Fenchel–Moreau theorem (Theorem 12.2), applied to each $Fu$. -/
theorem theorem_33_1_inversion (hF : ConvexBifun F) (u : Rn m) (x : Rn n) :
    convexCl (F u) x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - bifunBracket F (u, y) :=
  congrFun (convexCl_eq_convexConj_bracket (Bx := pairing n) hF u) x

/-- **Theorem 33.1** of [rockafellar1970convex], converse, convexity. Let $K$ be a concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$. Then the bifunction $F$ defined by
$Fu = K(u, \cdot)^*$ is convex. -/
theorem theorem_33_1_convexBifun (hK : ConcaveConvexFn K) : ConvexBifun (bifunOfSaddleFn K) :=
  convexBifun_bifunOfSaddle hK (pairing n)

/-- **Theorem 33.1** of [rockafellar1970convex], converse, image-closedness. For every $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the bifunction $F$ defined by
$Fu = K(u, \cdot)^*$ is image-closed: each $Fu$ is a closed function, because it is a conjugate.

**Reading.** Every reconstructed slice is closed without a saddle hypothesis.
-/
theorem theorem_33_1_imageClosed (K : Rn m × Rn n → EReal) :
    ImageClosedBifun (bifunOfSaddleFn K) :=
  imageClosedBifun_bifunOfSaddle

/-- **Theorem 33.1** of [rockafellar1970convex], converse, the bracket. Let $K$ be a concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $Fu = K(u, \cdot)^*$. Then
$$\langle Fu, x^* \rangle = (\operatorname{cl}_2 K)(u, x^*) \quad \text{for all } (u, x^*),$$
where $\operatorname{cl}_2$ is the closure in the second (convex) argument. -/
theorem theorem_33_1_bracket_eq (hK : ConcaveConvexFn K) :
    bifunBracket (bifunOfSaddleFn K) = cl₂ K :=
  funext fun p => bracket_bifunOfSaddle (Bx := pairing n) hK p

end Thm331

/-! ### Corollary 33.1.1 -/

section Cor3311

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Corollary 33.1.1** of [rockafellar1970convex], concave-convexity of $\operatorname{cl}_1 K$.
If $K$ is a concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$, then
$\operatorname{cl}_1 K$ is concave-convex. -/
theorem corollary_33_1_1_cl₁_concaveConvex (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (cl₁ K) :=
  concaveConvexFn_partialCl₁ (pairing m) hK

/-- **Corollary 33.1.1** of [rockafellar1970convex], concave-convexity of $\operatorname{cl}_2 K$.
If $K$ is a concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$, then
$\operatorname{cl}_2 K$ is concave-convex. -/
theorem corollary_33_1_1_cl₂_concaveConvex (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (cl₂ K) :=
  concaveConvexFn_partialCl₂ (pairing n) hK

/-- **Corollary 33.1.1** of [rockafellar1970convex], closedness of $\operatorname{cl}_1 K$. For
every $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the function
$\operatorname{cl}_1 K$ is concave-closed: $\operatorname{cl}_1 \operatorname{cl}_1 K =
\operatorname{cl}_1 K$.

The concave closure is idempotent, so no hypothesis on $K$ is needed.

**Reading.** The first closure is closed in its first argument even for arbitrary functions.
-/
theorem corollary_33_1_1_cl₁_concaveClosed (K : Rn m × Rn n → EReal) :
    PartialClosed₁ (cl₁ K) :=
  partialClosed₁_partialCl₁ K

/-- **Corollary 33.1.1** of [rockafellar1970convex], closedness of $\operatorname{cl}_2 K$. For
every $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the function
$\operatorname{cl}_2 K$ is convex-closed: $\operatorname{cl}_2 \operatorname{cl}_2 K =
\operatorname{cl}_2 K$.

The convex closure is idempotent, so no hypothesis on $K$ is needed.

**Reading.** The second closure is closed in its second argument even for arbitrary functions.
-/
theorem corollary_33_1_1_cl₂_convexClosed (K : Rn m × Rn n → EReal) :
    PartialClosed₂ (cl₂ K) :=
  partialClosed₂_partialCl₂ K

end Cor3311


/-! ### Corollary 33.1.2 -/

section Cor3312

variable {m n : ℕ}

/-- A closed bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ is image-closed: each $Fu$ is a
closed function, because a slice of a closed function is closed. -/
theorem imageClosedBifun_of_closedConvexBifun {F : Bifun (Rn m) (Rn n)} (hF : ClosedConvexBifun F) :
    ImageClosedBifun F :=
  hF.imageClosedBifun

/-- **Corollary 33.1.2** of [rockafellar1970convex]. The relations
$$K(u, x^*) = \langle Fu, x^* \rangle, \qquad Fu = K(u, \cdot)^*$$
define a one-to-one correspondence between the image-closed convex bifunctions $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and the convex-closed concave-convex functions $K$ on
$\mathbb{R}^m \times \mathbb{R}^n$.

The correspondence is an `Equiv` between the two subtypes. Its forward map is
`Rockafellar.bifunBracket` (see `Rockafellar.corollary_33_1_2_apply`), and its inverse is
`Rockafellar.bifunOfSaddleFn` (see `Rockafellar.corollary_33_1_2_symm_apply`). It specializes
`ConvexAnalysis.bifunSaddleEquiv`. -/
noncomputable def corollary_33_1_2 :
    {F : Bifun (Rn m) (Rn n) // ConvexBifun F ∧ ImageClosedBifun F} ≃
      {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ PartialClosed₂ K} :=
  bifunSaddleEquiv (Bx := pairing n)

/-- The forward map of the correspondence of Corollary 33.1.2 sends $F$ to
$K(u, x^*) = \langle Fu, x^* \rangle$. -/
theorem corollary_33_1_2_apply
    (F : {F : Bifun (Rn m) (Rn n) // ConvexBifun F ∧ ImageClosedBifun F}) :
    (corollary_33_1_2 F).1 = bifunBracket F.1 := rfl

/-- The inverse map of the correspondence of Corollary 33.1.2 sends $K$ to the bifunction
$Fu = K(u, \cdot)^*$. -/
theorem corollary_33_1_2_symm_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ PartialClosed₂ K}) :
    (corollary_33_1_2.symm K).1 = bifunOfSaddleFn K.1 := rfl

end Cor3312

/-! ### Corollary 33.1.3 -/

section Cor3313

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 33.1.3** of [rockafellar1970convex], convex argument. Let $F$ be a polyhedral convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then for each $u \in \mathbb{R}^m$, the
function $x^* \mapsto \langle Fu, x^* \rangle$ is polyhedral convex. -/
theorem corollary_33_1_3_convex (hF : PolyhedralBifun F) (u : Rn m) :
    PolyhedralFn fun y => bifunBracket F (u, y) :=
  polyhedralFn_bracket hF (pairing n) u

/-- **Corollary 33.1.3** of [rockafellar1970convex], concave argument. Let $F$ be a polyhedral
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then for each $x^* \in \mathbb{R}^n$,
the function $u \mapsto \langle Fu, x^* \rangle$ is polyhedral concave.

Polyhedral concavity is stated as polyhedral convexity of the negative,
$u \mapsto -\langle Fu, x^* \rangle$. -/
theorem corollary_33_1_3_concave (hF : PolyhedralBifun F) (y : Rn n) :
    PolyhedralFn fun u => -(bifunBracket F (u, y)) :=
  polyhedralFn_neg_bracket hF (pairing n) y

/-- **Corollary 33.1.3** of [rockafellar1970convex], inversion. Let $F$ be a proper polyhedral
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then for all $u$ and $x$,
$$(Fu)(x) = \sup_{x^*} \{\langle x, x^* \rangle - \langle Fu, x^* \rangle\}.$$

No closure is needed, because a proper polyhedral convex function is closed. Properness of $F$
is properness of its graph function, `ConvexAnalysis.ProperConvex (ConvexAnalysis.graphFn F)`. -/
theorem corollary_33_1_3_inversion (hF : PolyhedralBifun F) (hp : ProperConvex (graphFn F))
    (u : Rn m)
    (x : Rn n) :
    F u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - bifunBracket F (u, y) :=
  eq_iSup_sub_bracket_of_polyhedralBifun (pairing n) hF hp u x

end Cor3313

/-! ### The adjoint bracket -/

section AdjointBracket

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- For every bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, the function
$\langle u, F^* x^* \rangle$ is concave-convex in $(u, x^*)$. No hypothesis on $F$ is needed,
because the adjoint of every bifunction is concave.

**Reading.** The convex-to-concave adjoint yields a saddle bracket for arbitrary bifunctions.
-/
theorem adjointBracket_concaveConvex (F : Bifun (Rn m) (Rn n)) :
    ConcaveConvexFn (adjointBracket F) :=
  concaveConvexFn_concaveBracket (concaveBifun_convexAdjointBifun (pairing m) (pairing n) F)
      (pairing m)

/-- For a convex bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, the function
$\langle u, F^* x^* \rangle$ is concave-closed. By Theorem 33.2 it equals
$\operatorname{cl}_1 \langle Fu, x^* \rangle$, and every $\operatorname{cl}_1$ is concave-closed
by Corollary 33.1.1. -/
theorem adjointBracket_concaveClosed (hF : ConvexBifun F) :
    PartialClosed₁ (adjointBracket F) := by
  have h : adjointBracket F = cl₁ (bifunBracket F) :=
    (partialCl₁_bracket (pairing m) (pairing n) hF).symm
  rw [h]
  exact corollary_33_1_1_cl₁_concaveClosed _

end AdjointBracket

/-! ### Theorem 33.2 -/

section Thm332

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Theorem 33.2** of [rockafellar1970convex], first equation. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Then
$$\langle u, F^* x^* \rangle = \operatorname{cl}_1 \langle Fu, x^* \rangle \quad \text{for all }
  (u, x^*),$$
where $\operatorname{cl}_1$ is the closure in the first (concave) argument.

The proof is the concave Fenchel–Moreau theorem in $u$. -/
theorem theorem_33_2_first (hF : ConvexBifun F) : adjointBracket F = cl₁ (bifunBracket F) :=
  (partialCl₁_bracket (pairing m) (pairing n) hF).symm

/-- **Theorem 33.2** of [rockafellar1970convex], second equation. Let $F$ be a convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then
$$\operatorname{cl}_2 \langle u, F^* x^* \rangle = \langle (\operatorname{cl} F) u, x^* \rangle
  \quad \text{for all } (u, x^*),$$
where $\operatorname{cl}_2$ is the closure in the second (convex) argument.

The closure $\operatorname{cl} F$ is `ConvexAnalysis.convexClBifun F`. The proof applies the
first equation to $F^*$ and uses $F^{**} = \operatorname{cl} F$ (Theorem 30.1). -/
theorem theorem_33_2_second (hF : ConvexBifun F) :
    cl₂ (adjointBracket F) = bifunBracket (convexClBifun F) := by
  funext p
  exact congrFun
    (partialCl₂_concaveBracket_convexAdjointBifun (Bu := pairing m) (Bx := pairing n) hF p.1) p.2

end Thm332

/-! ### Corollary 33.2.1 -/

section Cor3321

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 33.2.1** of [rockafellar1970convex], first assertion. Let $F$ be a convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $u \in \operatorname{ri}(\operatorname{dom} F)$.
Then $\langle Fu, x^* \rangle = \langle u, F^* x^* \rangle$ for every $x^* \in \mathbb{R}^n$.

The two sides differ by $\operatorname{cl}_1$ (Theorem 33.2), which changes nothing on
$\operatorname{ri}(\operatorname{dom} F)$ by Theorem 7.4. The domain $\operatorname{dom} F$ is
`ConvexAnalysis.convexDomBifun F`, the set of $u$ for which $Fu$ is not identically $+\infty$. -/
theorem corollary_33_2_1_primal (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (convexDomBifun F))
    (y : Rn n) : bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint (pairing m) (pairing n) hF hu y

/-- **Corollary 33.2.1** of [rockafellar1970convex], second assertion. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $x^* \in
\operatorname{ri}(\operatorname{dom} F^*)$. Then $\langle Fu, x^* \rangle = \langle u, F^* x^*
\rangle$ for every $u \in \mathbb{R}^m$.

The domain $\operatorname{dom} F^*$ is `ConvexAnalysis.concaveDomBifun (Rockafellar.dualProgram
F)`, the set of $x^*$ for which $F^* x^*$ is not identically $-\infty$. The book says to apply
the first assertion to $F^*$. This is not literally possible, because $F^*$ is concave. The
proof here uses the closedness of $F$, which the rest of the corollary does not use. -/
theorem corollary_33_2_1_dual (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (u : Rn m) {y : Rn n}
    (hy : y ∈ ri (concaveDomBifun (dualProgram F))) :
    bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint_concaveDomBifun
    (Bu := pairing m) (Bx := pairing n) hF hcl u hy

end Cor3321

/-! ### Corollary 33.2.2 -/

section Cor3322

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 33.2.2** of [rockafellar1970convex]. Let $F$ be a proper polyhedral convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $u \in \mathbb{R}^m$ and
$x^* \in \mathbb{R}^n$ with $u \in \operatorname{dom} F$ or $x^* \in \operatorname{dom} F^*$.
Then
$$\langle Fu, x^* \rangle = \langle u, F^* x^* \rangle.$$

Polyhedrality removes the relative interiors of Corollary 33.2.1. Properness of $F$ is
properness of its graph function. -/
theorem corollary_33_2_2 (hF : PolyhedralBifun F) (hp : ProperConvex (graphFn F)) (u : Rn m)
    (y : Rn n)
    (h : u ∈ convexDomBifun F ∨ y ∈ concaveDomBifun (dualProgram F)) :
    bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_polyhedral (pairing m) (pairing n) hF hp u y h

/-- **Corollary 33.2.2** of [rockafellar1970convex], the parenthetical remark. Let $F$ be any
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $u \notin \operatorname{dom} F$ and
$x^* \notin \operatorname{dom} F^*$. Then $\langle Fu, x^* \rangle = -\infty$ and
$\langle u, F^* x^* \rangle = +\infty$.

Neither polyhedrality nor properness is used.

**Reading.** Opposite infinite values when both inputs are off their domains hold without
polyhedrality or properness.
-/
theorem corollary_33_2_2_exceptional {u : Rn m} (hu : u ∉ convexDomBifun F) {y : Rn n}
    (hy : y ∉ concaveDomBifun (dualProgram F)) :
    bifunBracket F (u, y) = ⊥ ∧ adjointBracket F (u, y) = ⊤ :=
  bracket_eq_bot_and_concaveBracket_eq_top (pairing m) (pairing n) hu hy

end Cor3322


/-! ### Full, lower and upper closedness -/

section Closedness

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- Let $K$ be a concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$ that is finite
everywhere. Then $K$ is convex-closed. This is Corollary 10.1.1, applied to each function
$K(u, \cdot)$. -/
theorem partialClosed₂_of_finite (hK : ConcaveConvexFn K) (hbot : ∀ p, K p ≠ ⊥)
    (htop : ∀ p, K p ≠ ⊤) : PartialClosed₂ K := by
  refine partialClosed₂_iff.2 fun u => ?_
  refine (closedConvex_iff_lowerSemicontinuous fun x => hbot (u, x)).2 ?_
  refine Continuous.lowerSemicontinuous
    (ConvexFn.continuous_of_convexDom_eq_univ (hK.convex_snd u) ⟨⟨0, ?_⟩, fun x => hbot (u, x)⟩ ?_)
  · exact lt_top_iff_ne_top.2 (htop (u, 0))
  · exact Set.eq_univ_of_forall fun x => lt_top_iff_ne_top.2 (htop (u, x))

/-- Let $K$ be a concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$ that is finite
everywhere. Then $K$ is fully closed: it is both convex-closed and concave-closed. -/
theorem fullyClosedFn_of_finite (hK : ConcaveConvexFn K) (hbot : ∀ p, K p ≠ ⊥)
    (htop : ∀ p, K p ≠ ⊤) : FullyClosedFn K := by
  refine ⟨partialClosed₂_of_finite hK hbot htop, ?_⟩
  have hswap : PartialClosed₂ (saddleSwap K) :=
    partialClosed₂_of_finite hK.saddleSwap
      (fun q => by simpa [saddleSwap] using htop (q.2, q.1))
      (fun q => by simpa [saddleSwap] using hbot (q.2, q.1))
  have h : saddleSwap (partialCl₁ K) = saddleSwap K := by
    rw [← partialCl₂_saddleSwap]
    exact hswap
  exact saddleSwap_injective h

/-- A function $K$ on $\mathbb{R}^m \times \mathbb{R}^n$ is fully closed (convex-closed and
concave-closed) if and only if it is both lower closed and upper closed. The proof uses the
idempotence of $\operatorname{cl}_1$ and $\operatorname{cl}_2$.

**Reading.** Both lower and upper closedness characterize full closedness for arbitrary functions.
-/
theorem fullyClosed_iff_lowerClosed_and_upperClosed (K : Rn m × Rn n → EReal) :
    FullyClosedFn K ↔ LowerClosedFn K ∧ UpperClosedFn K :=
  fullyClosedFn_iff

/-- **Section 33** of [rockafellar1970convex], the convention for convex-concave functions, lower
closure. For a convex-concave $K$ the book's $\operatorname{cl}_1$ closes the first argument
convexly and its $\operatorname{cl}_2$ closes the second argument concavely. Both are the
operators of this module conjugated by negation. So the book's "$K$ is lower closed" means
$-\operatorname{cl}_1 \operatorname{cl}_2 (-K) = K$, and this holds if and only if $-K$ is upper
closed. -/
theorem convexConcave_lowerClosed_iff (K : Rn m × Rn n → EReal) :
    (fun p => -(upperCl (fun q => -(K q)) p)) = K ↔ UpperClosedFn fun p => -(K p) := by
  constructor
  · intro h
    funext p
    rw [← congrFun h p, neg_neg]
  · intro h
    funext p
    rw [congrFun h p, neg_neg]

/-- **Section 33** of [rockafellar1970convex], the convention for convex-concave functions, upper
closure. The book's "$K$ is upper closed" for a convex-concave $K$ means $-\operatorname{cl}_2
\operatorname{cl}_1 (-K) = K$, and this holds if and only if $-K$ is lower closed. -/
theorem convexConcave_upperClosed_iff (K : Rn m × Rn n → EReal) :
    (fun p => -(lowerCl (fun q => -(K q)) p)) = K ↔ LowerClosedFn fun p => -(K p) := by
  constructor
  · intro h
    funext p
    rw [← congrFun h p, neg_neg]
  · intro h
    funext p
    rw [congrFun h p, neg_neg]

end Closedness

/-! ### Theorem 33.3 -/

section Thm333

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 33.3** of [rockafellar1970convex], one direction. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $K(u, x^*) = \langle Fu, x^* \rangle$ is
a lower closed concave-convex function.

Both closure steps are Theorem 33.2. -/
theorem theorem_33_3_lowerClosed (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    LowerClosedFn (bifunBracket F) :=
  lowerClosedFn_bracket (pairing m) (pairing n) hF hcl

/-- **Theorem 33.3** of [rockafellar1970convex]. The relations $K(u, x^*) = \langle Fu, x^* \rangle$
and $Fu = K(u, \cdot)^*$ define a one-to-one correspondence between the lower closed
concave-convex functions $K$ on $\mathbb{R}^m \times \mathbb{R}^n$ and the closed convex
bifunctions $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$. In the form stated here: for every lower
closed concave-convex $K$ there is exactly one closed convex bifunction $F$ with
$\langle Fu, x^* \rangle = K(u, x^*)$ for all $(u, x^*)$.

The other direction, that the bracket of a closed convex bifunction is lower closed, is
`Rockafellar.theorem_33_3_lowerClosed`. -/
theorem theorem_33_3 (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedConvexBifun F ∧ bifunBracket F = K :=
  exists_unique_convexBifun_bracket_eq (pairing m) (pairing n) hK hlc

end Thm333

/-! ### Corollary 33.3.1 -/

section Cor3331

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {Klow Kup : Rn m × Rn n → EReal}

/-- **Corollary 33.3.1** of [rockafellar1970convex], sufficiency. Let $\underline{K}$ be a
concave-convex function and $\overline{K}$ a function on $\mathbb{R}^m \times \mathbb{R}^n$ with
$\operatorname{cl}_1 \underline{K} = \overline{K}$ and $\operatorname{cl}_2 \overline{K} =
\underline{K}$. Then there is exactly one closed convex bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$ with
$$\underline{K}(u, x^*) = \langle Fu, x^* \rangle, \qquad \overline{K}(u, x^*) = \langle u, F^*
  x^* \rangle.$$

The book states that such an $F$ exists, and is then unique, if and only if the two closure
relations hold. The necessity is `Rockafellar.corollary_33_3_1_necessity_first` and
`Rockafellar.corollary_33_3_1_necessity_second`.

**Reading.** Requires concavity-convexity only of the lower function. The upper one is its first
closure.
-/
theorem corollary_33_3_1 (hK : ConcaveConvexFn Klow) (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedConvexBifun F ∧
      bifunBracket F = Klow ∧ adjointBracket F = Kup :=
  exists_unique_bifun_of_closure_pair (pairing m) (pairing n) hK h1 h2

/-- **Corollary 33.3.1** of [rockafellar1970convex], necessity, first relation. For a convex
bifunction $F$, $\operatorname{cl}_1 \langle Fu, x^* \rangle = \langle u, F^* x^* \rangle$. No
closedness of $F$ is needed.

**Reading.** The first closure relation holds without closedness of F.
-/
theorem corollary_33_3_1_necessity_first (hF : ConvexBifun F) :
    cl₁ (bifunBracket F) = adjointBracket F :=
  partialCl₁_bracket (pairing m) (pairing n) hF

/-- **Corollary 33.3.1** of [rockafellar1970convex], necessity, second relation. For a closed convex
bifunction $F$, $\operatorname{cl}_2 \langle u, F^* x^* \rangle = \langle Fu, x^* \rangle$. -/
theorem corollary_33_3_1_necessity_second (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    cl₂ (adjointBracket F) = bifunBracket F :=
  partialCl₂_concaveBracket_adjoint (pairing m) (pairing n) hF hcl

/-- **Corollary 33.3.1** of [rockafellar1970convex]. If $\operatorname{cl}_1 \underline{K} =
\overline{K}$ and $\operatorname{cl}_2 \overline{K} = \underline{K}$, then $\underline{K}$ is
lower closed.

**Reading.** The closure identities imply lower closedness without a saddle hypothesis.
-/
theorem corollary_33_3_1_lowerClosed (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    LowerClosedFn Klow := by
  have e1 : partialCl₁ Klow = Kup := h1
  have e2 : partialCl₂ Kup = Klow := h2
  rw [lowerClosedFn_iff, lowerCl_def, e1, e2]

/-- **Corollary 33.3.1** of [rockafellar1970convex]. If $\operatorname{cl}_1 \underline{K} =
\overline{K}$ and $\operatorname{cl}_2 \overline{K} = \underline{K}$, then $\overline{K}$ is
upper closed.

**Reading.** The closure identities imply upper closedness without a saddle hypothesis.
-/
theorem corollary_33_3_1_upperClosed (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    UpperClosedFn Kup := by
  have e1 : partialCl₁ Klow = Kup := h1
  have e2 : partialCl₂ Kup = Klow := h2
  rw [upperClosedFn_iff, upperCl_def, e2, e1]

/-- **Corollary 33.3.1** of [rockafellar1970convex]. If $\operatorname{cl}_2 \overline{K} =
\underline{K}$, then $\underline{K} \le \overline{K}$. Only this relation is used, because
$\operatorname{cl}_2$ does not increase a function.

**Reading.** The second closure identity alone gives the pointwise order.
-/
theorem corollary_33_3_1_le (h2 : cl₂ Kup = Klow) : Klow ≤ Kup :=
  le_of_partialCl₂_eq h2

end Cor3331

/-! ### Corollary 33.3.2 -/

section Cor3332

variable {m n : ℕ}

/-- **Corollary 33.3.2** of [rockafellar1970convex]. The relations
$$\overline{K} = \operatorname{cl}_1 \underline{K}, \qquad \underline{K} = \operatorname{cl}_2
  \overline{K}$$
define a one-to-one correspondence between the lower closed concave-convex functions
$\underline{K}$ and the upper closed concave-convex functions $\overline{K}$ on
$\mathbb{R}^m \times \mathbb{R}^n$.

The correspondence is an `Equiv` between the two subtypes, with forward map
$\operatorname{cl}_1$ (`Rockafellar.corollary_33_3_2_apply`) and inverse $\operatorname{cl}_2$
(`Rockafellar.corollary_33_3_2_symm_apply`). It specializes
`ConvexAnalysis.lowerUpperClosedEquiv`. -/
noncomputable def corollary_33_3_2 :
    {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ LowerClosedFn K} ≃
      {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ UpperClosedFn K} :=
  lowerUpperClosedEquiv (pairing m) (pairing n)

/-- The forward map of the correspondence of Corollary 33.3.2 sends $\underline{K}$ to
$\overline{K} = \operatorname{cl}_1 \underline{K}$. -/
theorem corollary_33_3_2_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ LowerClosedFn K}) :
    (corollary_33_3_2 K).1 = cl₁ K.1 := rfl

/-- The inverse map of the correspondence of Corollary 33.3.2 sends $\overline{K}$ to
$\underline{K} = \operatorname{cl}_2 \overline{K}$. -/
theorem corollary_33_3_2_symm_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ UpperClosedFn K}) :
    (corollary_33_3_2.symm K).1 = cl₂ K.1 := rfl

end Cor3332

/-!
### Corollary 33.3.3

The book asks for $K$ to be "finite continuous" on $C \times D$, which means jointly continuous. The
hypotheses below ask only for convexity, concavity and continuity of each one-variable section on
its own set.
-/

section Cor3333

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

private theorem dom₂_concaveBifunBracket (G : Bifun (Rn n) (Rn m)) :
    dom₂ (concaveBifunBracket G) = concaveDomBifun G := by
  ext y
  constructor
  · intro hy
    have h : y ∈ convexDom fun w => concaveBracket (pairing m) G (0 : Rn m) w := hy 0
    rwa [convexDom_concaveBracket] at h
  · intro hy u
    have h : y ∈ convexDom fun w => concaveBracket (pairing m) G u w := by
      rw [convexDom_concaveBracket]; exact hy
    exact h

/-- **Corollary 33.3.3** of [rockafellar1970convex], lower closedness. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be non-empty closed sets, and let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be such that $K(u, \cdot)$ is continuous on $D$
for each $u \in C$ and $K(\cdot, x^*)$ is continuous on $C$ for each $x^* \in D$. Then the lower
simple extension $\underline{K}$ of $K$ is lower closed.

The lower simple extension `ConvexAnalysis.lowerSimpleExt C D K` is $K$ on $C \times D$,
$+\infty$ on $C \times (\mathbb{R}^n \setminus D)$ and $-\infty$ for $u \notin C$.

**Reading.** Separate continuity suffices, without sectional convexity or concavity.
-/
theorem corollary_33_3_3_lowerClosed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    LowerClosedFn (lowerSimpleExt C D K) :=
  lowerClosedFn_lowerSimpleExt hCcl hDcl hCne hDne hcontD hcontC

/-- **Corollary 33.3.3** of [rockafellar1970convex], upper closedness. Under the hypotheses of
`Rockafellar.corollary_33_3_3_lowerClosed`, the upper simple extension $\overline{K}$ of $K$ is
upper closed.

The upper simple extension `ConvexAnalysis.upperSimpleExt C D K` is $K$ on $C \times D$,
$-\infty$ on $(\mathbb{R}^m \setminus C) \times D$ and $+\infty$ for $x^* \notin D$.

**Reading.** Separate continuity suffices, without sectional convexity or concavity.
-/
theorem corollary_33_3_3_upperClosed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    UpperClosedFn (upperSimpleExt C D K) :=
  upperClosedFn_upperSimpleExt hCcl hDcl hCne hDne hcontD hcontC

/-- **Corollary 33.3.3** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be non-empty closed convex sets, and let $K : \mathbb{R}^m \times
\mathbb{R}^n \to \mathbb{R}$ be such that $K(u, \cdot)$ is convex and continuous on $D$ for each
$u \in C$, and $K(\cdot, x^*)$ is concave and continuous on $C$ for each $x^* \in D$. Let
$\underline{K}$ and $\overline{K}$ be the lower and the upper simple extensions of $K$. Then
there is exactly one closed convex bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ with
$$\underline{K}(u, x^*) = \langle Fu, x^* \rangle, \qquad \overline{K}(u, x^*) = \langle u, F^*
  x^* \rangle.$$

**Generalization.** The book assumes that $K$ is finite and continuous on $C \times D$, which
means jointly continuous. Here only each one-variable section is assumed continuous.

The convexity of $D$ is part of the hypothesis `ConvexOn ℝ D`. The bifunction is
$Fu = \underline{K}(u, \cdot)^*$; see `Rockafellar.corollary_33_3_3_bracket` and the
declarations after it. -/
theorem corollary_33_3_3 (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedConvexBifun F ∧
      bifunBracket F = lowerSimpleExt C D K ∧ adjointBracket F = upperSimpleExt C D K :=
  exists_unique_bifun_of_simpleExt (pairing m) (pairing n) hC hCcl hDcl hCne ⟨hconc, hconv⟩ hDne
    hcontD hcontC

/-- **Corollary 33.3.3** of [rockafellar1970convex], the bifunction. Let $C$ be convex, $D$ closed,
and $K$ real-valued with $K(u, \cdot)$ convex and continuous on $D$ for $u \in C$ and
$K(\cdot, x^*)$ concave on $C$ for $x^* \in D$. Then the bifunction
$Fu = \underline{K}(u, \cdot)^*$ satisfies $\langle Fu, x^* \rangle = \underline{K}(u, x^*)$.

**Reading.** Only continuity in the second argument is needed for the lower bracket identity.
-/
theorem corollary_33_3_3_bracket (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) :
    bifunBracket (bifunOfSaddleFn (lowerSimpleExt C D K)) = lowerSimpleExt C D K :=
  (theorem_33_1_bracket_eq (concaveConvexFn_lowerSimpleExt hC ⟨hconc, hconv⟩)).trans
    (partialCl₂_lowerSimpleExt hDcl hcontD)

/-- **Corollary 33.3.3** of [rockafellar1970convex], the adjoint. Let $C$ be non-empty, closed and
convex, $D$ closed, and $K$ real-valued with $K(u, \cdot)$ convex and continuous on $D$ for
$u \in C$ and $K(\cdot, x^*)$ concave and continuous on $C$ for $x^* \in D$. Then the bifunction
$Fu = \underline{K}(u, \cdot)^*$ satisfies $\langle u, F^* x^* \rangle = \overline{K}(u, x^*)$.

**Reading.** Uses separate continuity and allows an empty D.
-/
theorem corollary_33_3_3_adjointBracket (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    adjointBracket (bifunOfSaddleFn (lowerSimpleExt C D K)) = upperSimpleExt C D K := by
  rw [theorem_33_2_first
      (theorem_33_1_convexBifun (concaveConvexFn_lowerSimpleExt hC ⟨hconc, hconv⟩)),
    corollary_33_3_3_bracket hC hDcl hconv hconc hcontD]
  exact partialCl₁_lowerSimpleExt hCcl hCne hcontC

/-- **Corollary 33.3.3** of [rockafellar1970convex], $\operatorname{dom} F = C$. Let $C$ be convex,
$D$ closed and non-empty, and $K$ real-valued with $K(u, \cdot)$ convex and continuous on $D$
for $u \in C$ and $K(\cdot, x^*)$ concave on $C$ for $x^* \in D$. Then the bifunction
$Fu = \underline{K}(u, \cdot)^*$ has $\operatorname{dom} F = C$.

**Reading.** Needs closedness, continuity and nonemptiness in the second coordinate only, apart from
convexity assumptions.
-/
theorem corollary_33_3_3_dom (hC : Convex ℝ C) (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) :
    convexDomBifun (bifunOfSaddleFn (lowerSimpleExt C D K)) = C := by
  have h1 : dom₁ (bifunBracket (bifunOfSaddleFn (lowerSimpleExt C D K)))
      = convexDomBifun (bifunOfSaddleFn (lowerSimpleExt C D K)) :=
    dom₁_bracket (pairing n) _
  rw [← h1, corollary_33_3_3_bracket hC hDcl hconv hconc hcontD, dom₁_lowerSimpleExt hDne]

/-- **Corollary 33.3.3** of [rockafellar1970convex], $\operatorname{dom} F^* = D$. Let $C$ be
non-empty, closed and convex, $D$ closed, and $K$ real-valued with $K(u, \cdot)$ convex and
continuous on $D$ for $u \in C$ and $K(\cdot, x^*)$ concave and continuous on $C$ for
$x^* \in D$. Then the bifunction $Fu = \underline{K}(u, \cdot)^*$ has
$\operatorname{dom} F^* = D$.

**Reading.** Separate continuity suffices and an empty D is allowed.
-/
theorem corollary_33_3_3_domAdjoint (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    concaveDomBifun (dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K))) = D := by
  have h2 : dom₂ (adjointBracket (bifunOfSaddleFn (lowerSimpleExt C D K)))
      = concaveDomBifun (dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K))) :=
    dom₂_concaveBifunBracket _
  rw [← h2, corollary_33_3_3_adjointBracket hC hCcl hDcl hCne hconv hconc hcontD hcontC,
    dom₂_upperSimpleExt hCne]

/-- **Corollary 33.3.3** of [rockafellar1970convex], the formula for $F$ off $C$. For $u \notin C$,
the bifunction $Fu = \underline{K}(u, \cdot)^*$ has $(Fu)(x) = +\infty$ for every $x$. No
hypothesis on $K$ is needed. -/
theorem corollary_33_3_3_bifun_of_notMem {u : Rn m} (hu : u ∉ C) (x : Rn n) :
    bifunOfSaddleFn (lowerSimpleExt C D K) u x = ⊤ := by
  rw [bifunOfSaddleFn_apply]
  refine le_antisymm le_top (le_iSup_of_le 0 ?_)
  rw [lowerSimpleExt_of_notMem_left (p := (u, (0 : Rn n))) hu]
  simp

/-- **Corollary 33.3.3** of [rockafellar1970convex], the formula for $F$ on $C$. For $u \in C$, the
bifunction $Fu = \underline{K}(u, \cdot)^*$ has
$$(Fu)(x) = \sup \{\langle x, x^* \rangle - K(u, x^*) \mid x^* \in D\}.$$
No hypothesis on $K$ is needed. -/
theorem corollary_33_3_3_bifun_of_mem {u : Rn m} (hu : u ∈ C) (x : Rn n) :
    bifunOfSaddleFn (lowerSimpleExt C D K) u x
      = ⨆ y ∈ D, (((pairing n x y : ℝ) : EReal) - ((K (u, y) : ℝ) : EReal)) := by
  rw [bifunOfSaddleFn_apply]
  refine iSup_congr fun y => ?_
  by_cases hy : y ∈ D
  · rw [lowerSimpleExt_of_mem (p := (u, y)) hu hy, iSup_pos hy]
  · rw [lowerSimpleExt_of_notMem_right (p := (u, y)) hu hy, iSup_neg hy]
    simp

/-- **Corollary 33.3.3** of [rockafellar1970convex], the formula for $F^*$ on $D$. Let $C$ be
convex, $D$ closed, and $K$ real-valued with $K(u, \cdot)$ convex and continuous on $D$ for
$u \in C$ and $K(\cdot, x^*)$ concave on $C$ for $x^* \in D$. For $x^* \in D$, the adjoint of
$Fu = \underline{K}(u, \cdot)^*$ has
$$(F^* x^*)(u^*) = \inf \{\langle u, u^* \rangle - K(u, x^*) \mid u \in C\}.$$

**Reading.** The formula uses the infimum over C and needs only continuity in the second argument.
-/
theorem corollary_33_3_3_adjoint_of_mem (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) {y : Rn n} (hy : y ∈ D) (v : Rn m) :
    dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = ⨅ u ∈ C, (((pairing m u v : ℝ) : EReal) - ((K (u, y) : ℝ) : EReal)) := by
  have hbr := congrFun (corollary_33_3_3_bracket hC hDcl hconv hconc hcontD)
  have h : dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = concaveConj (pairing m)
        (fun u => bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y) v :=
    convexAdjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) _ y v
  rw [h, concaveConj_apply]
  refine iInf_congr fun u => ?_
  rw [show bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y
      = lowerSimpleExt C D K (u, y) from hbr (u, y)]
  by_cases hu : u ∈ C
  · rw [lowerSimpleExt_of_mem (p := (u, y)) hu hy, iInf_pos hu]
  · rw [lowerSimpleExt_of_notMem_left (p := (u, y)) hu, iInf_neg hu]
    simp

/-- **Corollary 33.3.3** of [rockafellar1970convex], the formula for $F^*$ off $D$. Let $C$ be
non-empty and convex, $D$ closed, and $K$ real-valued with $K(u, \cdot)$ convex and continuous
on $D$ for $u \in C$ and $K(\cdot, x^*)$ concave on $C$ for $x^* \in D$. For $x^* \notin D$, the
adjoint of $Fu = \underline{K}(u, \cdot)^*$ has $(F^* x^*)(u^*) = -\infty$ for every $u^*$.

**Reading.** The formula gives negative infinity using only continuity in the second argument.
-/
theorem corollary_33_3_3_adjoint_of_notMem (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) {y : Rn n} (hy : y ∉ D) (v : Rn m) :
    dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v = ⊥ := by
  have hbr := congrFun (corollary_33_3_3_bracket hC hDcl hconv hconc hcontD)
  have h : dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = concaveConj (pairing m)
        (fun u => bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y) v :=
    convexAdjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) _ y v
  obtain ⟨u, hu⟩ := hCne
  rw [h, concaveConj_apply]
  refine le_antisymm (iInf_le_of_le u ?_) bot_le
  rw [show bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y
      = lowerSimpleExt C D K (u, y) from hbr (u, y),
    lowerSimpleExt_of_notMem_right (p := (u, y)) hu hy]
  simp

end Cor3333

end Rockafellar
