/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.Rockafellar.Common.Euclidean
import NumlibSurface.Rockafellar.Chapter07.Section33

/-!
# Rockafellar, Section 34: Closures and equivalence classes

This module formalizes Section 34 of [rockafellar1970convex] (pp. 359–369). For a function $K$ on
$\mathbb{R}^m \times \mathbb{R}^n$, the section studies the lower closure
$\operatorname{cl}_2 \operatorname{cl}_1 K$ and the upper closure
$\operatorname{cl}_1 \operatorname{cl}_2 K$, the effective domain $\operatorname{dom} K =
\operatorname{dom}_1 K \times \operatorname{dom}_2 K$, and the notions of equivalent, closed and
proper saddle-functions. Two saddle-functions $K$ and $L$ are equivalent if
$\operatorname{cl}_1 K = \operatorname{cl}_1 L$ and $\operatorname{cl}_2 K = \operatorname{cl}_2 L$.
The central result is Theorem 34.2: for a closed convex bifunction $F$, the class $\Omega(F)$ of
concave-convex functions $K$ with $\langle Fu, x^* \rangle \le K(u, x^*) \le \langle u, F^* x^*
\rangle$ is exactly one equivalence class of closed saddle-functions, and every such class has this
form. The section then characterizes closedness through the slices of $K$ (Theorem 34.3), and
describes an equivalence class by the kernel of its members, the restriction to
$\operatorname{ri}(\operatorname{dom} K)$ (Theorems 34.4 and 34.5). The proofs specialize the
backbone modules `Numlib.Analysis.Convex.Saddle.Equiv` and `Numlib.Analysis.Convex.Saddle.Kernel`.

## Coverage

All 10 numbered results of Section 34 are formalized: Theorems 34.1–34.5, Corollaries 34.2.1–34.2.4
and Corollary 34.5.1. Theorem 34.3 is formalized in its six clauses (a)–(f) and as an equivalence.

## Main definitions

* Theorem 34.2, `Rockafellar.Ω`: for a bifunction $F$, the set of concave-convex $K$ with $\langle
  Fu, x^* \rangle \le K(u, x^*) \le \langle u, F^* x^* \rangle$.

## Main results

* Section 34, `Rockafellar.dom₁_eq`, `Rockafellar.dom₂_eq`, `Rockafellar.domSaddle_eq`,
  `Rockafellar.properSaddleFn_iff`, `Rockafellar.saddleEquiv_iff`, `Rockafellar.closedSaddleFn_iff`:
  the definitions of the section, that is $\operatorname{dom} K = \operatorname{dom}_1 K \times
  \operatorname{dom}_2 K$, proper, equivalent and closed saddle-functions.
* Theorem 34.1, `Rockafellar.theorem_34_1_lower`, `Rockafellar.theorem_34_1_upper`,
  `Rockafellar.theorem_34_1_lower_eq`, `Rockafellar.theorem_34_1_upper_eq`: the lower closure is
  lower closed and the upper closure is upper closed.
* Theorem 34.2, `Rockafellar.theorem_34_2_lower_mem` and the declarations after it: for a closed
  convex bifunction $F$, $\Omega(F)$ is one equivalence class of closed saddle-functions with least
  member $\langle Fu, x^* \rangle$ and greatest member $\langle u, F^* x^* \rangle$; $F$ and $F^*$
  are recovered from every member; and every equivalence class of closed concave-convex functions is
  some $\Omega(F)$.
* Corollary 34.2.1, `Rockafellar.corollary_34_2_1_dom`,
  `Rockafellar.corollary_34_2_1_eq_of_mem_relint_dom₁`,
  `Rockafellar.corollary_34_2_1_eq_of_mem_relint_dom₂`: equivalent proper saddle-functions have the
  same effective domain, and closed ones agree where one argument lies in the relative interior of
  its domain.
* Corollary 34.2.2, `Rockafellar.corollary_34_2_2_of_lowerClosed` and the declarations after it:
  lower closed, upper closed and fully closed saddle-functions are closed; the class of a closed $K$
  has exactly one lower closed member, $\operatorname{cl}_2 K$, which is its least member, and
  exactly one upper closed member, $\operatorname{cl}_1 K$, which is its greatest member.
* Corollary 34.2.3, `Rockafellar.corollary_34_2_3`, `Rockafellar.corollary_34_2_3_not_equiv`: the
  only improper closed saddle-functions are the constants $-\infty$ and $+\infty$, and these are not
  equivalent.
* Corollary 34.2.4, `Rockafellar.corollary_34_2_4_mem_iff` and the declarations after it: the
  extensions of a finite function $K$ on $C \times D$ by $+\infty$ on
  $C \times (\mathbb{R}^n \setminus D)$ and $-\infty$ on $(\mathbb{R}^m \setminus C) \times D$ form
  one equivalence class of closed proper saddle-functions.
* Theorem 34.3, `Rockafellar.theorem_34_3_a` to `Rockafellar.theorem_34_3_f`,
  `Rockafellar.theorem_34_3`: a proper concave-convex function is closed if and only if its slices
  behave in a prescribed way on $\operatorname{ri} C$, on $C \setminus \operatorname{ri} C$ and off
  $C$, and dually on $D$.
* Section 34, `Rockafellar.kernel_eq_convexRestrict`, `Rockafellar.kernel_eq_iff'`,
  `Rockafellar.simpleSaddleFn_iff`, `Rockafellar.simpleSaddleFn_of_closed`,
  `Rockafellar.simpleSaddleFn_bifunBracket`: the kernel and the simple saddle-functions.
* Theorem 34.4, `Rockafellar.theorem_34_4`: two closed proper concave-convex functions are
  equivalent if and only if they have the same kernel.
* Theorem 34.5, `Rockafellar.theorem_34_5` and the declarations before it: the kernel of a simple
  proper concave-convex function is the kernel of exactly one equivalence class of closed proper
  concave-convex functions.
* Corollary 34.5.1, `Rockafellar.corollary_34_5_1`: a finite concave-convex function on the product
  of two non-empty convex sets $C \times D$ determines, through its restriction to
  $\operatorname{ri}(C \times D)$, exactly one equivalence class of closed proper concave-convex
  functions.

## Conventions

* The orientation of $\operatorname{cl}_1$ and $\operatorname{cl}_2$ is that of
  `NumlibSurface.Rockafellar.Chapter07.Section33`. The lower closure is `ConvexAnalysis.lowerCl K`,
  equal to $\operatorname{cl}_2 \operatorname{cl}_1 K$, and the upper closure is
  `ConvexAnalysis.upperCl K`, equal to $\operatorname{cl}_1 \operatorname{cl}_2 K$.
* For a bifunction $F$, $\underline{K}(u, x^*) = \langle Fu, x^* \rangle$ is
  `Rockafellar.bifunBracket F` and $\overline{K}(u, x^*) = \langle u, F^* x^* \rangle$ is
  `Rockafellar.adjointBracket F`.
* The order interval $\{K \mid K_1 \le K \le K_2\}$ is `ConvexAnalysis.saddleClass K₁ K₂`. Unlike
  $\Omega(F)$, it does not require its members to be concave-convex.

## Implementation notes

* Theorem 34.2 comes before Theorem 34.1 in this module. The natural primitive is a closed convex
  bifunction $F$, whose class $\Omega(F)$ is one equivalence class of closed concave-convex
  functions, and Theorem 34.1 then says that the two closures of $K$ give such a pair.
* The kernel of $K$ is a function on all of $\mathbb{R}^m \times \mathbb{R}^n$: it is $K$ on
  $\operatorname{ri}(\operatorname{dom} K)$ and $+\infty$ elsewhere. So equality of kernels is one
  equation, `ConvexAnalysis.kernel K = ConvexAnalysis.kernel L`.

## Deviations from the source

* **Theorem 34.1** (generalization). The lower closure is lower closed and the upper closure is
  upper closed for every function $K$, with no hypothesis of concave-convexity or properness. See
  `Rockafellar.theorem_34_1_lower`.
* **Theorem 34.2**, the domain clause (correction). The factor statements
  $\operatorname{dom}_1 K = \operatorname{dom} F$ and $\operatorname{dom}_2 K = \operatorname{dom}
  F^*$ assume that the other factor of $\operatorname{dom} K$ is non-empty, and $\operatorname{dom}
  K = \operatorname{dom} F \times \operatorname{dom} F^*$ assumes that $K$ is proper. See
  `Rockafellar.theorem_34_2_dom₁`.
* **Corollary 34.2.1**, the domain clause (generalization). The book assumes that $K$ is closed. The
  equality of the effective domains needs no closedness. See `Rockafellar.corollary_34_2_1_dom`.
* **Corollary 34.2.4** (generalization). The book assumes that $K$ is continuous on $C \times D$,
  jointly. Here only each one-variable section is assumed continuous. See
  `Rockafellar.corollary_34_2_4_equiv`.

## Not formalized

* **The exercise that every $K(u, x^*) = \langle Fu, x^* \rangle$ is simple**, for an arbitrary
  convex or concave bifunction $F$. Only the case of a closed convex $F$ with $K$ proper is
  formalized, as `Rockafellar.simpleSaddleFn_bifunBracket`.
-/

namespace Rockafellar

open ConvexAnalysis

/-! ### The definitions of Section 34 -/

section Vocabulary

variable {m n : ℕ}

/-- **Section 34** of [rockafellar1970convex], definition of $\operatorname{dom}_1 K$. For $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$,
$$\operatorname{dom}_1 K = \{u \mid K(u, v) > -\infty \text{ for all } v\}.$$
-/
theorem dom₁_eq (K : Rn m × Rn n → EReal) : dom₁ K = {u | ∀ v, ⊥ < K (u, v)} := rfl

/-- **Section 34** of [rockafellar1970convex], definition of $\operatorname{dom}_2 K$. For $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$,
$$\operatorname{dom}_2 K = \{v \mid K(u, v) < +\infty \text{ for all } u\}.$$
-/
theorem dom₂_eq (K : Rn m × Rn n → EReal) : dom₂ K = {v | ∀ u, K (u, v) < ⊤} := rfl

/-- **Section 34** of [rockafellar1970convex], definition of the effective domain. The effective
domain of a saddle-function $K$ on $\mathbb{R}^m \times \mathbb{R}^n$ is $\operatorname{dom} K =
\operatorname{dom}_1 K \times \operatorname{dom}_2 K$. -/
theorem domSaddle_eq (K : Rn m × Rn n → EReal) : domSaddle K = dom₁ K ×ˢ dom₂ K := rfl

/-- **Section 34** of [rockafellar1970convex], definition of a proper saddle-function. A
saddle-function $K$ on $\mathbb{R}^m \times \mathbb{R}^n$ is **proper** if and only if
$\operatorname{dom} K \neq \emptyset$. -/
theorem properSaddleFn_iff (K : Rn m × Rn n → EReal) :
    ProperSaddleFn K ↔ (domSaddle K).Nonempty :=
  properSaddleFn_iff_domSaddle_nonempty

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ and
$(u, v) \in \operatorname{dom} K$, the value $K(u, v)$ is finite. -/
theorem lt_top_of_mem_domSaddle' {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}
    (hp : p ∈ domSaddle K) : ⊥ < K p ∧ K p < ⊤ :=
  ⟨bot_lt_of_mem_domSaddle hp, lt_top_of_mem_domSaddle hp⟩

variable {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- Let $C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be non-empty and let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$. Then the lower simple extension of $K$ has
effective domain $C \times D$; in particular it is proper. -/
theorem domSaddle_lowerSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    domSaddle (lowerSimpleExt C D K) = C ×ˢ D := by
  have h : domSaddle (lowerSimpleExt C D K)
      = dom₁ (lowerSimpleExt C D K) ×ˢ dom₂ (lowerSimpleExt C D K) := rfl
  rw [h, dom₁_lowerSimpleExt hDne, dom₂_lowerSimpleExt hCne]

/-- Let $C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be non-empty and let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$. Then the upper simple extension of $K$ has
effective domain $C \times D$; in particular it is proper. -/
theorem domSaddle_upperSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    domSaddle (upperSimpleExt C D K) = C ×ˢ D := by
  have h : domSaddle (upperSimpleExt C D K)
      = dom₁ (upperSimpleExt C D K) ×ˢ dom₂ (upperSimpleExt C D K) := rfl
  rw [h, dom₁_upperSimpleExt hDne, dom₂_upperSimpleExt hCne]

/-- **Section 34** of [rockafellar1970convex], definition of equivalence. Two functions $K$ and $L$
on $\mathbb{R}^m \times \mathbb{R}^n$ are **equivalent** if and only if
$\operatorname{cl}_1 K = \operatorname{cl}_1 L$ and
$\operatorname{cl}_2 K = \operatorname{cl}_2 L$. -/
theorem saddleEquiv_iff (K L : Rn m × Rn n → EReal) :
    SaddleEquiv K L ↔ cl₁ K = cl₁ L ∧ cl₂ K = cl₂ L := Iff.rfl

/-- **Section 34** of [rockafellar1970convex], definition of a closed saddle-function. A function
$K$ on $\mathbb{R}^m \times \mathbb{R}^n$ is **closed** if and only if
$$\operatorname{cl}_1 \operatorname{cl}_2 K = \operatorname{cl}_1 K, \qquad \operatorname{cl}_2
  \operatorname{cl}_1 K = \operatorname{cl}_2 K.$$

The book defines $K$ to be closed if $\operatorname{cl}_1 K$ and $\operatorname{cl}_2 K$ are
both equivalent to $K$, and then reduces this to the two equations. -/
theorem closedSaddleFn_iff (K : Rn m × Rn n → EReal) :
    ClosedSaddleFn K ↔ cl₁ (cl₂ K) = cl₁ K ∧ cl₂ (cl₁ K) = cl₂ K := Iff.rfl

end Vocabulary

/-! ### Theorem 34.2 -/

section Thm342

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Theorem 34.2** of [rockafellar1970convex], the class $\Omega(F)$. For a bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$, $\Omega(F)$ is the set of all concave-convex functions $K$ on
$\mathbb{R}^m \times \mathbb{R}^n$ with
$$\langle Fu, x^* \rangle \le K(u, x^*) \le \langle u, F^* x^* \rangle \quad \text{for all } (u,
  x^*).$$

The book defines $\Omega(F)$ for a closed convex bifunction $F$. The concave-convexity is part
of the book's definition. The backbone `ConvexAnalysis.bifunSaddleClass` is the order interval
`ConvexAnalysis.saddleClass` between the same two brackets, without the condition of
concave-convexity; `Rockafellar.mem_bifunSaddleClass_of_mem_Ω` gives the inclusion. -/
noncomputable def Ω (F : Bifun (Rn m) (Rn n)) : Set (Rn m × Rn n → EReal) :=
  {K | ConcaveConvexFn K} ∩ saddleClass (bifunBracket F) (adjointBracket F)

/-- A function $K$ is in $\Omega(F)$ if and only if $K$ is concave-convex and $\langle Fu, x^*
\rangle \le K(u, x^*) \le \langle u, F^* x^* \rangle$ for all $(u, x^*)$. -/
theorem mem_Ω : K ∈ Ω F ↔ ConcaveConvexFn K ∧ bifunBracket F ≤ K ∧ K ≤ adjointBracket F :=
  Iff.rfl

/-- Every member of $\Omega(F)$ is in the backbone class `ConvexAnalysis.bifunSaddleClass` of $F$
for the Euclidean pairings. The statements about a class in Section 37 are phrased with the
backbone class. -/
theorem mem_bifunSaddleClass_of_mem_Ω (hK : K ∈ Ω F) :
    K ∈ bifunSaddleClass (pairing m) (pairing n) F := hK.2

/-- **Theorem 34.2** of [rockafellar1970convex], the least member. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $\underline{K}(u, x^*) = \langle Fu, x^*
\rangle$ belongs to $\Omega(F)$. -/
theorem theorem_34_2_lower_mem (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    bifunBracket F ∈ Ω F :=
  ⟨theorem_33_1_concaveConvex hF,
    mem_saddleClass_left (corollary_33_3_1_necessity_second hF hcl)⟩

/-- **Theorem 34.2** of [rockafellar1970convex], the greatest member. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $\overline{K}(u, x^*) = \langle u, F^*
x^* \rangle$ belongs to $\Omega(F)$. -/
theorem theorem_34_2_upper_mem (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    adjointBracket F ∈ Ω F :=
  ⟨adjointBracket_concaveConvex F,
    mem_saddleClass_right (corollary_33_3_1_necessity_second hF hcl)⟩

/-- **Theorem 34.2** of [rockafellar1970convex], second equation. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then every $K \in \Omega(F)$ satisfies
$\operatorname{cl}_2 K = \underline{K}$, that is, $(\operatorname{cl}_2 K)(u, x^*) = \langle Fu,
x^* \rangle$. -/
theorem theorem_34_2_cl₂ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    cl₂ K = bifunBracket F :=
  partialCl₂_eq_bracket_of_mem_saddleClass (pairing m) (pairing n) hF hcl hK.2

/-- **Theorem 34.2** of [rockafellar1970convex], first equation. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Then every $K \in \Omega(F)$ satisfies
$\operatorname{cl}_1 K = \overline{K}$, that is, $(\operatorname{cl}_1 K)(u, x^*) = \langle u,
F^* x^* \rangle$.

No closedness of $F$ is needed. -/
theorem theorem_34_2_cl₁ (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    cl₁ K = adjointBracket F :=
  partialCl₁_eq_concaveBracket_of_mem_saddleClass (pairing m) (pairing n) hF hK.2

/-- **Theorem 34.2** of [rockafellar1970convex], closedness. Let $F$ be a closed convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then every $K \in \Omega(F)$ is a closed saddle-function. -/
theorem theorem_34_2_closed (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    ClosedSaddleFn K :=
  closedSaddleFn_of_mem_saddleClass_bracket (pairing m) (pairing n) hF hcl hK.2

/-- **Theorem 34.2** of [rockafellar1970convex], equivalence. Let $F$ be a closed convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then any two members $K, L \in \Omega(F)$ are equivalent. -/
theorem theorem_34_2_equiv (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hL : L ∈ Ω F) : SaddleEquiv K L :=
  saddleEquiv_of_mem_saddleClass (corollary_33_3_1_necessity_first hF)
    (corollary_33_3_1_necessity_second hF hcl) hK.2 hL.2

/-- **Theorem 34.2** of [rockafellar1970convex], maximality. Let $F$ be a closed convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$, and let $L$ be a concave-convex
function equivalent to $K$. Then $L \in \Omega(F)$. So $\Omega(F)$ is a whole equivalence class. -/
theorem theorem_34_2_maximal (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) : L ∈ Ω F := by
  refine ⟨hL, ?_⟩
  have e2 : partialCl₂ L = bifunBracket F := by
    have hK2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
    rw [← h.2]; exact hK2
  have e1 : partialCl₁ L = adjointBracket F := by
    have hK1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
    rw [← h.1]; exact hK1
  have hmem := mem_saddleClass_self L
  rw [e1, e2] at hmem
  exact hmem

/-- **Theorem 34.2** of [rockafellar1970convex], converse. Let $K$ be a closed concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$. Then there is exactly one closed convex
bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ with
$$\langle Fu, x^* \rangle = (\operatorname{cl}_2 K)(u, x^*), \qquad \langle u, F^* x^* \rangle =
  (\operatorname{cl}_1 K)(u, x^*).$$
-/
theorem theorem_34_2_converse (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedConvexBifun F ∧
      bifunBracket F = cl₂ K ∧ adjointBracket F = cl₁ K :=
  exists_unique_bifun_of_closedSaddleFn (pairing m) (pairing n) hK hcl

/-- **Theorem 34.2** of [rockafellar1970convex], converse, membership. Let $K$ be a concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $F$ be a bifunction with $\langle Fu,
x^* \rangle = (\operatorname{cl}_2 K)(u, x^*)$ and $\langle u, F^* x^* \rangle =
(\operatorname{cl}_1 K)(u, x^*)$. Then $K \in \Omega(F)$. With
`Rockafellar.theorem_34_2_converse`, this shows that every equivalence class of closed
concave-convex functions is some $\Omega(F)$. -/
theorem theorem_34_2_mem_self (hK : ConcaveConvexFn K) (hlow : bifunBracket F = cl₂ K)
    (hup : adjointBracket F = cl₁ K) : K ∈ Ω F := by
  refine ⟨hK, ?_⟩
  have e2 : partialCl₂ K = bifunBracket F := hlow.symm
  have e1 : partialCl₁ K = adjointBracket F := hup.symm
  have hmem := mem_saddleClass_self K
  rw [e1, e2] at hmem
  exact hmem

/-- **Theorem 34.2** of [rockafellar1970convex], domain, first factor. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$ with
$\operatorname{dom}_2 K \neq \emptyset$. Then $\operatorname{dom}_1 K = \operatorname{dom} F$.

**Correction.** The book states $\operatorname{dom} K = \operatorname{dom} F \times
\operatorname{dom} F^*$ and argues the two factors separately, without the hypothesis
$\operatorname{dom}_2 K \neq \emptyset$. The statement here needs this hypothesis. -/
theorem theorem_34_2_dom₁ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hne : (dom₂ K).Nonempty) : dom₁ K = convexDomBifun F :=
  dom₁_eq_convexDomBifun_of_mem_bifunSaddleClass (pairing m) (pairing n) hF hcl hK.2 hK.1 hne

private theorem dom₂_adjointBracket (F : Bifun (Rn m) (Rn n)) :
    dom₂ (adjointBracket F) = concaveDomBifun (dualProgram F) := by
  ext y
  constructor
  · intro hy
    have h : y ∈ convexDom fun w => concaveBracket (pairing m) (dualProgram F) (0 : Rn m) w := hy 0
    rwa [convexDom_concaveBracket] at h
  · intro hy u
    have h : y ∈ convexDom fun w => concaveBracket (pairing m) (dualProgram F) u w := by
      rw [convexDom_concaveBracket]; exact hy
    exact h

/-- **Theorem 34.2** of [rockafellar1970convex], domain, second factor. Let $F$ be a convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$ with
$\operatorname{dom}_1 K \neq \emptyset$. Then $\operatorname{dom}_2 K = \operatorname{dom} F^*$.

**Correction.** As for `Rockafellar.theorem_34_2_dom₁`, the book does not have the hypothesis
$\operatorname{dom}_1 K \neq \emptyset$.

The domain $\operatorname{dom} F^*$ is the set of $x^*$ for which $F^* x^*$ is not identically
$-\infty$. -/
theorem theorem_34_2_dom₂ (hF : ConvexBifun F) (hK : K ∈ Ω F) (hne : (dom₁ K).Nonempty) :
    dom₂ K = concaveDomBifun (dualProgram F) := by
  have e1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  rw [← dom₂_partialCl₁ hK.1 hne, e1, dom₂_adjointBracket]

/-- **Theorem 34.2** of [rockafellar1970convex], domain. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$ be proper. Then
$$\operatorname{dom} K = \operatorname{dom} F \times \operatorname{dom} F^*.$$

**Correction.** The book does not assume that $K$ is proper. The hypothesis supplies the
non-emptiness hypotheses of `Rockafellar.theorem_34_2_dom₁` and `Rockafellar.theorem_34_2_dom₂`. -/
theorem theorem_34_2_dom (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) :
    domSaddle K = convexDomBifun F ×ˢ concaveDomBifun (dualProgram F) := by
  have h : domSaddle K = dom₁ K ×ˢ dom₂ K := rfl
  rw [h, theorem_34_2_dom₁ hF hcl hK hp.dom₂_nonempty,
    theorem_34_2_dom₂ hF hK hp.dom₁_nonempty]

/-- **Theorem 34.2** of [rockafellar1970convex], recovery of $F$. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $K \in \Omega(F)$. Then $F$ is
recovered from $K$ as $Fu = K(u, \cdot)^*$. -/
theorem theorem_34_2_bifunOfSaddleFn (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) :
    bifunOfSaddleFn K = F := by
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  refine eq_of_bracket_eq (Bx := pairing n) (theorem_33_1_convexBifun hK.1) hF
    (theorem_33_1_imageClosed K) (imageClosedBifun_of_closedConvexBifun hcl) ?_
  funext u x
  calc bracket (pairing n) (bifunOfSaddleFn K) u x
      = partialCl₂ K (u, x) := bracket_bifunOfSaddle hK.1 (u, x)
    _ = bracket (pairing n) F u x := congrFun h2 (u, x)

/-- **Theorem 34.2** of [rockafellar1970convex], third equation. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $K \in \Omega(F)$. Then for all $u$ and
$x$,
$$(Fu)(x) = \sup_{x^*} \{\langle x, x^* \rangle - K(u, x^*)\}.$$
-/
theorem theorem_34_2_bifun_apply (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (u : Rn m) (x : Rn n) :
    F u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - K (u, y) := by
  rw [← theorem_34_2_bifunOfSaddleFn hF hcl hK]
  exact bifunOfSaddleFn_apply K u x

/-- **Theorem 34.2** of [rockafellar1970convex], fourth equation. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $K \in \Omega(F)$. Then for all $x^*$
and $u^*$,
$$(F^* x^*)(u^*) = \inf_u \{\langle u, u^* \rangle - K(u, x^*)\}.$$

The book obtains this from the third equation by symmetry, but the situation is not symmetric:
$F^* x^*$ is the concave conjugate of $u \mapsto (\operatorname{cl}_2 K)(u, x^*)$, and the
closedness of $K$ is what allows $\operatorname{cl}_2 K$ to be replaced by $K$ under the
conjugate. -/
theorem theorem_34_2_adjoint (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (x : Rn n) (v : Rn m) :
    dualProgram F x v = ⨅ u : Rn m, ((pairing m u v : ℝ) : EReal) - K (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have hfun : (fun u => bracket (pairing n) F u x) = fun u => partialCl₂ K (u, x) := by
    funext u
    exact (congrFun h2 (u, x)).symm
  have hclc : concaveCl (fun u => partialCl₂ K (u, x)) = concaveCl fun u => K (u, x) := by
    rw [← partialCl₁_slice (partialCl₂ K) x, ← partialCl₁_slice K x, hcls.1]
  have hgoal : convexAdjointBifun (pairing m) (pairing n) F x v
      = ⨅ u : Rn m, ((pairing m u v : ℝ) : EReal) - K (u, x) := by
    rw [convexAdjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) F x v, hfun,
      ← concaveConj_concaveCl (fun u => partialCl₂ K (u, x)), hclc, concaveConj_concaveCl,
      concaveConj_apply]
  exact hgoal

/-- **Theorem 34.2** of [rockafellar1970convex], last clause, first half. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be proper, and let
$u \in \operatorname{ri}(\operatorname{dom} F)$. Then for every $x^*$,
$$K(u, x^*) = \langle Fu, x^* \rangle = \langle u, F^* x^* \rangle.$$
-/
theorem theorem_34_2_eq_of_mem_relint_dom₁ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {u : Rn m} (hu : u ∈ ri (convexDomBifun F)) (x : Rn n) :
    K (u, x) = bifunBracket F (u, x) ∧ K (u, x) = adjointBracket F (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have h1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  have hu' : u ∈ ri (dom₁ K) := by
    rw [theorem_34_2_dom₁ hF hcl hK hp.dom₂_nonempty]; exact hu
  have heq := hcls.eq_partialCl₂_of_mem_relint_dom₁ hK.1 hp hu' x
  refine ⟨heq.trans (congrFun h2 (u, x)), ?_⟩
  rw [heq, ← hcls.partialCl₁_eq_partialCl₂_of_mem_relint_dom₁ hK.1 hp hu' x]
  exact congrFun h1 (u, x)

/-- **Theorem 34.2** of [rockafellar1970convex], last clause, second half. Let $F$ be a closed
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be proper, and
let $x^* \in \operatorname{ri}(\operatorname{dom} F^*)$. Then for every $u$,
$$K(u, x^*) = \langle Fu, x^* \rangle = \langle u, F^* x^* \rangle.$$
-/
theorem theorem_34_2_eq_of_mem_relint_dom₂ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {x : Rn n}
    (hx : x ∈ ri (concaveDomBifun (dualProgram F))) (u : Rn m) :
    K (u, x) = bifunBracket F (u, x) ∧ K (u, x) = adjointBracket F (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have h1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  have hx' : x ∈ ri (dom₂ K) := by
    rw [theorem_34_2_dom₂ hF hK hp.dom₁_nonempty]; exact hx
  have heq := hcls.eq_partialCl₂_of_mem_relint_dom₂ hK.1 hp hx' u
  refine ⟨heq.trans (congrFun h2 (u, x)), ?_⟩
  rw [heq, ← hcls.partialCl₁_eq_partialCl₂_of_mem_relint_dom₂ hK.1 hp hx' u]
  exact congrFun h1 (u, x)

end Thm342

/-!
### Theorem 34.1

The two closure operations always give a pair $\operatorname{cl}_2 \operatorname{cl}_1 K$,
$\operatorname{cl}_1 \operatorname{cl}_2 K$ of the kind in Corollary 33.3.1, and so a class
$\Omega(F)$.
-/

section Thm341

variable {m n : ℕ}

/-- **Theorem 34.1** of [rockafellar1970convex], lower closure. For every function $K$ on
$\mathbb{R}^m \times \mathbb{R}^n$, the lower closure
$\operatorname{cl}_2 \operatorname{cl}_1 K$ is lower closed.

**Generalization.** The statement needs no hypothesis on $K$: neither concave-convexity nor
properness. It follows from the monotonicity and the idempotence of the two closures. -/
theorem theorem_34_1_lower (K : Rn m × Rn n → EReal) : LowerClosedFn (lowerCl K) :=
  lowerCl_idem K

/-- **Theorem 34.1** of [rockafellar1970convex], upper closure. For every function $K$ on
$\mathbb{R}^m \times \mathbb{R}^n$, the upper closure
$\operatorname{cl}_1 \operatorname{cl}_2 K$ is upper closed.

**Generalization.** As for `Rockafellar.theorem_34_1_lower`, no hypothesis on $K$ is needed. -/
theorem theorem_34_1_upper (K : Rn m × Rn n → EReal) : UpperClosedFn (upperCl K) :=
  upperCl_idem K

/-- **Theorem 34.1** of [rockafellar1970convex], first displayed equation. For every function $K$ on
$\mathbb{R}^m \times \mathbb{R}^n$,
$$\operatorname{cl}_2 \operatorname{cl}_1 \operatorname{cl}_2 \operatorname{cl}_1 K =
  \operatorname{cl}_2 \operatorname{cl}_1 K.$$
-/
theorem theorem_34_1_lower_eq (K : Rn m × Rn n → EReal) :
    cl₂ (cl₁ (cl₂ (cl₁ K))) = cl₂ (cl₁ K) := by
  have h : partialCl₂ (partialCl₁ (partialCl₂ (partialCl₁ K))) = partialCl₂ (partialCl₁ K) :=
    lowerCl_idem K
  exact h

/-- **Theorem 34.1** of [rockafellar1970convex], second displayed equation. For every function $K$
on $\mathbb{R}^m \times \mathbb{R}^n$,
$$\operatorname{cl}_1 \operatorname{cl}_2 \operatorname{cl}_1 \operatorname{cl}_2 K =
  \operatorname{cl}_1 \operatorname{cl}_2 K.$$
-/
theorem theorem_34_1_upper_eq (K : Rn m × Rn n → EReal) :
    cl₁ (cl₂ (cl₁ (cl₂ K))) = cl₁ (cl₂ K) := by
  have h : partialCl₁ (partialCl₂ (partialCl₁ (partialCl₂ K))) = partialCl₁ (partialCl₂ K) :=
    upperCl_idem K
  exact h

end Thm341

/-! ### Corollary 34.2.1 -/

section Cor3421

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Corollary 34.2.1** of [rockafellar1970convex], first clause. Let $K$ and $L$ be equivalent
proper concave-convex functions on $\mathbb{R}^m \times \mathbb{R}^n$. Then
$\operatorname{dom} L = \operatorname{dom} K$.

**Generalization.** The book assumes that $K$ is closed. This clause needs no closedness. -/
theorem corollary_34_2_1_dom (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    domSaddle L = domSaddle K :=
  (h.domSaddle_eq hK hpK hL hpL).symm

/-- **Corollary 34.2.1** of [rockafellar1970convex], first clause, factor by factor. Let $K$ and $L$
be equivalent proper concave-convex functions on $\mathbb{R}^m \times \mathbb{R}^n$. Then
$\operatorname{dom}_1 L = \operatorname{dom}_1 K$ and $\operatorname{dom}_2 L =
\operatorname{dom}_2 K$.

No closedness is needed, although the blanket hypothesis "$K$ closed" of the book suggests that
it is: $\operatorname{dom}_1 K = \operatorname{dom}_1 (\operatorname{cl}_2 K)$ and
$\operatorname{dom}_2 K = \operatorname{dom}_2 (\operatorname{cl}_1 K)$, so equivalence alone
gives both factors. -/
theorem corollary_34_2_1_dom_of_not_closed (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    dom₁ L = dom₁ K ∧ dom₂ L = dom₂ K :=
  ⟨(h.dom₁_eq hK hpK hL hpL).symm, (h.dom₂_eq hK hpK hL hpL).symm⟩

/-- **Corollary 34.2.1** of [rockafellar1970convex], second clause, first argument. Let $K$ and $L$
be equivalent closed proper concave-convex functions on $\mathbb{R}^m \times \mathbb{R}^n$, and
let $u \in \operatorname{ri}(\operatorname{dom}_1 K)$. Then $L(u, v) = K(u, v)$ for every $v$. -/
theorem corollary_34_2_1_eq_of_mem_relint_dom₁ (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) {u : Rn m} (hu : u ∈ ri (dom₁ K))
    (v : Rn n) : L (u, v) = K (u, v) :=
  (h.eq_of_mem_relint_dom₁ hclK hK hpK hclL hL hpL hu v).symm

/-- **Corollary 34.2.1** of [rockafellar1970convex], second clause, second argument. Let $K$ and $L$
be equivalent closed proper concave-convex functions on $\mathbb{R}^m \times \mathbb{R}^n$, and
let $v \in \operatorname{ri}(\operatorname{dom}_2 K)$. Then $L(u, v) = K(u, v)$ for every $u$. -/
theorem corollary_34_2_1_eq_of_mem_relint_dom₂ (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) {v : Rn n} (hv : v ∈ ri (dom₂ K))
    (u : Rn m) : L (u, v) = K (u, v) :=
  (h.eq_of_mem_relint_dom₂ hclK hK hpK hclL hL hpL hv u).symm

end Cor3421

/-! ### Corollary 34.2.2 -/

section Cor3422

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Corollary 34.2.2** of [rockafellar1970convex]. A lower closed function on
$\mathbb{R}^m \times \mathbb{R}^n$ is closed. -/
theorem corollary_34_2_2_of_lowerClosed (h : LowerClosedFn K) : ClosedSaddleFn K :=
  h.closedSaddleFn

/-- **Corollary 34.2.2** of [rockafellar1970convex]. An upper closed function on
$\mathbb{R}^m \times \mathbb{R}^n$ is closed. -/
theorem corollary_34_2_2_of_upperClosed (h : UpperClosedFn K) : ClosedSaddleFn K :=
  h.closedSaddleFn

/-- **Corollary 34.2.2** of [rockafellar1970convex]. A fully closed function on
$\mathbb{R}^m \times \mathbb{R}^n$, one that is both convex-closed and concave-closed, is
closed. -/
theorem corollary_34_2_2_of_fullyClosed (h : FullyClosedFn K) : ClosedSaddleFn K :=
  (fullyClosedFn_iff.1 h).1.closedSaddleFn

/-- **Corollary 34.2.2** of [rockafellar1970convex], existence of a lower closed member. If $K$ is
closed, then $\operatorname{cl}_2 K$ is lower closed. Since $\operatorname{cl}_2 K$ is
equivalent to $K$, the class of $K$ has a lower closed member. -/
theorem corollary_34_2_2_lower_exists (hcl : ClosedSaddleFn K) : LowerClosedFn (cl₂ K) :=
  hcl.lowerClosedFn_partialCl₂

/-- **Corollary 34.2.2** of [rockafellar1970convex], existence of an upper closed member. If $K$ is
closed, then $\operatorname{cl}_1 K$ is upper closed. Since $\operatorname{cl}_1 K$ is
equivalent to $K$, the class of $K$ has an upper closed member. -/
theorem corollary_34_2_2_upper_exists (hcl : ClosedSaddleFn K) : UpperClosedFn (cl₁ K) :=
  hcl.upperClosedFn_partialCl₁

/-- **Corollary 34.2.2** of [rockafellar1970convex], uniqueness of the lower closed member. If $L$
is equivalent to $K$ and lower closed, then $L = \operatorname{cl}_2 K$. -/
theorem corollary_34_2_2_lower_unique (h : SaddleEquiv K L) (hL : LowerClosedFn L) : L = cl₂ K :=
  h.eq_partialCl₂_of_lowerClosedFn hL

/-- **Corollary 34.2.2** of [rockafellar1970convex], uniqueness of the upper closed member. If $L$
is equivalent to $K$ and upper closed, then $L = \operatorname{cl}_1 K$. -/
theorem corollary_34_2_2_upper_unique (h : SaddleEquiv K L) (hL : UpperClosedFn L) : L = cl₁ K :=
  h.eq_partialCl₁_of_upperClosedFn hL

/-- **Corollary 34.2.2** of [rockafellar1970convex], the least member. If $L$ is equivalent to $K$
and lower closed, then $L \le K$. So the lower closed member is the least member of the class. -/
theorem corollary_34_2_2_least (h : SaddleEquiv K L) (hL : LowerClosedFn L) : L ≤ K := by
  have e : L = partialCl₂ K := h.eq_partialCl₂_of_lowerClosedFn hL
  rw [e]
  exact partialCl₂_le K

/-- **Corollary 34.2.2** of [rockafellar1970convex], the greatest member. If $L$ is equivalent to
$K$ and upper closed, then $K \le L$. So the upper closed member is the greatest member of the
class. -/
theorem corollary_34_2_2_greatest (h : SaddleEquiv K L) (hL : UpperClosedFn L) : K ≤ L := by
  have e : L = partialCl₁ K := h.eq_partialCl₁_of_upperClosedFn hL
  rw [e]
  exact le_partialCl₁ K

end Cor3422

/-! ### Corollary 34.2.3 -/

section Cor3423

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Corollary 34.2.3** of [rockafellar1970convex]. Let $K$ be a closed function on
$\mathbb{R}^m \times \mathbb{R}^n$ that is not proper. Then $K$ is the constant $-\infty$ or the
constant $+\infty$. -/
theorem corollary_34_2_3 (hcl : ClosedSaddleFn K) (hp : ¬ ProperSaddleFn K) :
    K = (fun _ => (⊥ : EReal)) ∨ K = fun _ => (⊤ : EReal) :=
  hcl.eq_const_of_not_properSaddleFn hp

/-- **Corollary 34.2.3** of [rockafellar1970convex], last sentence. The constant functions $-\infty$
and $+\infty$ on $\mathbb{R}^m \times \mathbb{R}^n$ are not equivalent. -/
theorem corollary_34_2_3_not_equiv :
    ¬ SaddleEquiv (fun _ : Rn m × Rn n => (⊥ : EReal)) (fun _ => (⊤ : EReal)) :=
  not_saddleEquiv_const_bot_const_top

end Cor3423

/-!
### Corollary 34.2.4

The pattern of infinite values depends on the orientation: the extensions are $+\infty$ where
$u \in C$ and $v \notin D$, and $-\infty$ where $u \notin C$ and $v \in D$. A convention for
convex-concave functions would give the opposite pattern.
-/

section Cor3424

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}
  {L : Rn m × Rn n → EReal}

/-- **Corollary 34.2.4** of [rockafellar1970convex], the class. Let $C \subseteq \mathbb{R}^m$,
$D \subseteq \mathbb{R}^n$ and $K : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$. A function
$L$ lies between the lower and the upper simple extensions of $K$ if and only if
$$L = K \text{ on } C \times D, \qquad L = +\infty \text{ on } C \times (\mathbb{R}^n \setminus
  D), \qquad L = -\infty \text{ on } (\mathbb{R}^m \setminus C) \times D.$$
The values on $(\mathbb{R}^m \setminus C) \times (\mathbb{R}^n \setminus D)$ are arbitrary.

The class is the order interval `ConvexAnalysis.saddleClass`, without the condition of
concave-convexity that the book's $\Omega$ also contains. -/
theorem corollary_34_2_4_mem_iff :
    L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) ↔
      (∀ u ∈ C, ∀ v ∈ D, L (u, v) = (K (u, v) : EReal)) ∧
        (∀ u ∈ C, ∀ v ∉ D, L (u, v) = ⊤) ∧ ∀ u ∉ C, ∀ v ∈ D, L (u, v) = ⊥ :=
  mem_saddleClass_simpleExt_iff

/-- **Corollary 34.2.4** of [rockafellar1970convex], closedness. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be non-empty closed sets, and let $K : \mathbb{R}^m \times
\mathbb{R}^n \to \mathbb{R}$ be such that $K(u, \cdot)$ is continuous on $D$ for each $u \in C$
and $K(\cdot, v)$ is continuous on $C$ for each $v \in D$. Then every $L$ between the lower and
the upper simple extensions of $K$ is a closed saddle-function.

**Generalization.** The book assumes that $K$ is continuous on $C \times D$, jointly. Here only
each one-variable section is assumed continuous. -/
theorem corollary_34_2_4_closed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) : ClosedSaddleFn L :=
  closedSaddleFn_of_mem_saddleClass_simpleExt hCcl hDcl hCne hDne hcontD hcontC hL

/-- **Corollary 34.2.4** of [rockafellar1970convex], properness. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be non-empty and $K : \mathbb{R}^m \times \mathbb{R}^n \to
\mathbb{R}$. Then every $L$ between the lower and the upper simple extensions of $K$ is proper. -/
theorem corollary_34_2_4_proper (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) : ProperSaddleFn L :=
  properSaddleFn_of_mem_saddleClass_simpleExt hCne hDne hL

/-- **Corollary 34.2.4** of [rockafellar1970convex], one equivalence class. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be non-empty closed sets, and let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be such that $K(u, \cdot)$ is continuous on $D$
for each $u \in C$ and $K(\cdot, v)$ is continuous on $C$ for each $v \in D$. Then a function
$L$ lies between the lower and the upper simple extensions of $K$ if and only if $L$ is
equivalent to the lower simple extension.

**Generalization.** The book assumes that $K$ is continuous on $C \times D$, jointly. Here only
each one-variable section is assumed continuous. -/
theorem corollary_34_2_4_equiv (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C) :
    L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) ↔
      SaddleEquiv (lowerSimpleExt C D K) L :=
  mem_saddleClass_simpleExt_iff_saddleEquiv hCcl hDcl hCne hDne hcontD hcontC

/-- **Corollary 34.2.4** of [rockafellar1970convex], the least member. Let
$C \subseteq \mathbb{R}^m$, let $D \subseteq \mathbb{R}^n$ be non-empty and closed, and let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be such that $K(u, \cdot)$ is continuous on $D$
for each $u \in C$. Then the lower simple extension of $K$ belongs to the class, so it is its
least member. -/
theorem corollary_34_2_4_least (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D) :
    lowerSimpleExt C D K ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) :=
  mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)

/-- **Corollary 34.2.4** of [rockafellar1970convex], the greatest member. Let
$C \subseteq \mathbb{R}^m$, let $D \subseteq \mathbb{R}^n$ be non-empty and closed, and let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be such that $K(u, \cdot)$ is continuous on $D$
for each $u \in C$. Then the upper simple extension of $K$ belongs to the class, so it is its
greatest member. -/
theorem corollary_34_2_4_greatest (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D) :
    upperSimpleExt C D K ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) :=
  mem_saddleClass_right (partialCl₂_upperSimpleExt hDcl hDne hcontD)

end Cor3424

/-!
### Theorem 34.3

Each of the six clauses has one declaration, for the direction from closedness to the clause. The
converse needs all six clauses together and is `Rockafellar.theorem_34_3`. In this part,
$C = \operatorname{dom}_1 K$ and $D = \operatorname{dom}_2 K$.
-/

section Thm343

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Theorem 34.3(a)** of [rockafellar1970convex]. Let $K$ be a closed proper concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $u \in \operatorname{ri} C$. Then
$K(u, \cdot)$ is a closed proper convex function with effective domain $D$. -/
theorem theorem_34_3_a (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∈ ri (dom₁ K)) :
    ConvexFn (fun v => K (u, v)) ∧ ClosedConvex (fun v => K (u, v)) ∧
      ProperConvex (fun v => K (u, v)) ∧ convexDom (fun v => K (u, v)) = dom₂ K := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.convex_snd u, hs.1.closedConvex_slice u hu,
    hs.1.properConvex_slice u (intrinsicInterior_subset hu), hs.1.convexDom_slice u hu⟩

/-- **Theorem 34.3(b)** of [rockafellar1970convex]. Let $K$ be a closed proper concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $u \in C \setminus \operatorname{ri} C$.
Then $K(u, \cdot)$ is a proper convex function, and its effective domain $D_u$ satisfies
$D \subseteq D_u \subseteq \operatorname{cl} D$.

The inclusion $D \subseteq D_u$ holds for every $u$, by the definition of $D$. Only the other
inclusion uses the hypotheses. -/
theorem theorem_34_3_b (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∈ dom₁ K \ ri (dom₁ K)) :
    ConvexFn (fun v => K (u, v)) ∧ ProperConvex (fun v => K (u, v)) ∧
      dom₂ K ⊆ convexDom (fun v => K (u, v)) ∧
      convexDom (fun v => K (u, v)) ⊆ closure (dom₂ K) := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.convex_snd u, hs.1.properConvex_slice u hu.1, dom₂_subset_convexDom_slice K u,
    hs.1.convexDom_slice_subset_closure u hu.1⟩

/-- **Theorem 34.3(c)** of [rockafellar1970convex]. Let $K$ be a closed proper concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $u \notin C$. Then $K(u, \cdot)$ is an
improper convex function, $K(u, v) = -\infty$ for every $v \in \operatorname{ri} D$, and if
moreover $u \notin \operatorname{cl} C$, then $K(u, v) = -\infty$ for every $v \in D$. -/
theorem theorem_34_3_c (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∉ dom₁ K) :
    ¬ ProperConvex (fun v => K (u, v)) ∧ (∀ v ∈ ri (dom₂ K), K (u, v) = ⊥) ∧
      (u ∉ closure (dom₁ K) → ∀ v ∈ dom₂ K, K (u, v) = ⊥) := by
  have hs := hcl.saddleStructure hK hp
  have hbot : ∀ v ∈ ri (dom₂ K), K (u, v) = ⊥ := hs.1.eq_bot_of_notMem_dom₁ u hu
  refine ⟨?_, hbot, fun hu' => hs.1.eq_bot_of_notMem_closure_dom₁ u hu'⟩
  obtain ⟨v₀, hv₀⟩ := hp.relint_dom₂_nonempty hK
  exact fun hpr => hpr.ne_bot v₀ (hbot v₀ hv₀)

/-- **Theorem 34.3(d)** of [rockafellar1970convex]. Let $K$ be a closed proper concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $v \in \operatorname{ri} D$. Then
$K(\cdot, v)$ is a closed proper concave function with effective domain $C$. -/
theorem theorem_34_3_d (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∈ ri (dom₂ K)) :
    ConcaveFn (fun u => K (u, v)) ∧ ClosedConcave (fun u => K (u, v)) ∧
      ProperConcave (fun u => K (u, v)) ∧ concaveDom (fun u => K (u, v)) = dom₁ K := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.concave_fst v, hs.closedConcave_slice hv,
    hs.properConcave_slice (intrinsicInterior_subset hv), hs.concaveDom_slice hv⟩

/-- **Theorem 34.3(e)** of [rockafellar1970convex]. Let $K$ be a closed proper concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $v \in D \setminus \operatorname{ri} D$.
Then $K(\cdot, v)$ is a proper concave function, and its effective domain $C_v$ satisfies
$C \subseteq C_v \subseteq \operatorname{cl} C$. -/
theorem theorem_34_3_e (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∈ dom₂ K \ ri (dom₂ K)) :
    ConcaveFn (fun u => K (u, v)) ∧ ProperConcave (fun u => K (u, v)) ∧
      dom₁ K ⊆ concaveDom (fun u => K (u, v)) ∧
      concaveDom (fun u => K (u, v)) ⊆ closure (dom₁ K) := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.concave_fst v, hs.properConcave_slice hv.1, dom₁_subset_concaveDom_slice K v,
    hs.concaveDom_slice_subset_closure hv.1⟩

/-- **Theorem 34.3(f)** of [rockafellar1970convex]. Let $K$ be a closed proper concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $v \notin D$. Then $K(\cdot, v)$ is an
improper concave function, $K(u, v) = +\infty$ for every $u \in \operatorname{ri} C$, and if
moreover $v \notin \operatorname{cl} D$, then $K(u, v) = +\infty$ for every $u \in C$. -/
theorem theorem_34_3_f (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∉ dom₂ K) :
    ¬ ProperConcave (fun u => K (u, v)) ∧ (∀ u ∈ ri (dom₁ K), K (u, v) = ⊤) ∧
      (v ∉ closure (dom₂ K) → ∀ u ∈ dom₁ K, K (u, v) = ⊤) := by
  have hs := hcl.saddleStructure hK hp
  have htop : ∀ u ∈ ri (dom₁ K), K (u, v) = ⊤ := fun _u hu => hs.eq_top_of_notMem_dom₂ hv hu
  refine ⟨?_, htop, fun hv' _u hu => hs.eq_top_of_notMem_closure_dom₂ hv' hu⟩
  obtain ⟨u₀, hu₀⟩ := hp.relint_dom₁_nonempty hK
  exact fun hpr => hpr.ne_top u₀ (htop u₀ hu₀)

/-- **Theorem 34.3** of [rockafellar1970convex]. Let $K$ be a proper concave-convex function on
$\mathbb{R}^m \times \mathbb{R}^n$, with $C = \operatorname{dom}_1 K$ and
$D = \operatorname{dom}_2 K$. Then $K$ is closed if and only if it has the properties (a)–(f):

* for $u \in C$, $K(u, \cdot)$ is a proper convex function whose effective domain lies in
  $\operatorname{cl} D$, and for $u \in \operatorname{ri} C$ it is moreover closed with
  effective domain $D$;
* for $u \notin C$, $K(u, v) = -\infty$ for all $v \in \operatorname{ri} D$, and for
  $u \notin \operatorname{cl} C$, $K(u, v) = -\infty$ for all $v \in D$;
* the same properties, with the roles of the two arguments exchanged, hold for the concave
  functions $K(\cdot, v)$, with $+\infty$ in place of $-\infty$.

The properties are bundled as `ConvexAnalysis.SaddleStructure K`: the properties (a)–(c), as
`ConvexAnalysis.ConvexSliceStructure`, for $K$ and for the function $(v, u) \mapsto -K(u, v)$
(`ConvexAnalysis.saddleSwap K`). For the second function they are the properties (d)–(f) of $K$. -/
theorem theorem_34_3 (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    ClosedSaddleFn K ↔ SaddleStructure K :=
  closedSaddleFn_iff_saddleStructure hK hp

end Thm343

/-! ### The kernel and simple saddle-functions -/

section Kernel

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- For every $K$ on $\mathbb{R}^m \times \mathbb{R}^n$, $\operatorname{ri}(\operatorname{dom} K) =
\operatorname{ri}(\operatorname{dom}_1 K) \times \operatorname{ri}(\operatorname{dom}_2 K)$. The
kernel of $K$ lives on this product. -/
theorem relint_domSaddle_eq_prod (K : Rn m × Rn n → EReal) :
    ri (domSaddle K) = ri (dom₁ K) ×ˢ ri (dom₂ K) :=
  relint_domSaddle K

/-- **Section 34** of [rockafellar1970convex], definition of the kernel. The **kernel** of $K$ is
its restriction to $\operatorname{ri}(\operatorname{dom} K)$. Here it is the function equal to
$K$ on $\operatorname{ri}(\operatorname{dom} K)$ and to $+\infty$ elsewhere.

The book's kernel is a partial function on a product set that depends on $K$. The extension by
$+\infty$ makes the equality of two kernels one equation instead of an equality of domains
together with an equality of values. -/
theorem kernel_eq_convexRestrict (K : Rn m × Rn n → EReal) :
    kernel K = ConvexAnalysis.convexRestrict (ri (domSaddle K)) K := by
  have h : kernel K = ConvexAnalysis.convexRestrict (kernelSet K) K := rfl
  rw [h, kernelSet_eq_relint_domSaddle]

/-- The kernels of $K$ and $L$ are equal if and only if $\operatorname{ri}(\operatorname{dom} K) =
\operatorname{ri}(\operatorname{dom} L)$ and $K = L$ on
$\operatorname{ri}(\operatorname{dom} K)$. These are the two facts of the book's definition of
equal kernels. -/
theorem kernel_eq_iff' :
    kernel K = kernel L ↔ kernelSet K = kernelSet L ∧ Set.EqOn K L (kernelSet K) :=
  kernel_eq_iff

/-- **Section 34** of [rockafellar1970convex], definition of a simple saddle-function. A function
$K$ on $\mathbb{R}^m \times \mathbb{R}^n$ is **simple** if and only if for every $u \in
\operatorname{ri}(\operatorname{dom}_1 K)$ the effective domain of the convex function
$K(u, \cdot)$ lies in $\operatorname{cl}(\operatorname{dom}_2 K)$, and for every $v \in
\operatorname{ri}(\operatorname{dom}_2 K)$ the effective domain of the concave function
$K(\cdot, v)$ lies in $\operatorname{cl}(\operatorname{dom}_1 K)$. -/
theorem simpleSaddleFn_iff (K : Rn m × Rn n → EReal) :
    SimpleSaddleFn K ↔
      ((∀ u ∈ ri (dom₁ K), convexDom (fun v => K (u, v)) ⊆ closure (dom₂ K)) ∧
        ∀ v ∈ ri (dom₂ K), concaveDom (fun u => K (u, v)) ⊆ closure (dom₁ K)) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Section 34** of [rockafellar1970convex]. Every closed proper concave-convex function is
simple. This follows from the clauses (b) and (e) of Theorem 34.3. -/
theorem simpleSaddleFn_of_closed (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : SimpleSaddleFn K :=
  hcl.simpleSaddleFn hK hp

/-- **Section 34** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be non-empty and let $K : \mathbb{R}^m \times \mathbb{R}^n \to
\mathbb{R}$. Then the lower and the upper simple extensions of $K$ are simple. -/
theorem simpleSaddleFn_lowerSimpleExt' {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}
    (hCne : C.Nonempty) (hDne : D.Nonempty) :
    SimpleSaddleFn (lowerSimpleExt C D K) ∧ SimpleSaddleFn (upperSimpleExt C D K) := by
  refine ⟨simpleSaddleFn_lowerSimpleExt hCne hDne, ?_⟩
  rw [upperSimpleExt_eq_saddleSwap]
  exact simpleSaddleFn_saddleSwap_iff.2 (simpleSaddleFn_lowerSimpleExt hDne hCne)

/-- **Section 34** of [rockafellar1970convex], an exercise of the book, in a special case. Let $F$
be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ such that
$K(u, x^*) = \langle Fu, x^* \rangle$ is proper. Then $K$ is simple.

The book states the exercise for every convex or concave bifunction $F$. Here $F$ is closed, so
that $K$ is closed (Theorem 33.3), and $K$ is proper, so that Theorem 34.3 applies. The
unrestricted statement is not formalized. -/
theorem simpleSaddleFn_bifunBracket {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hp : ProperSaddleFn (bifunBracket F)) :
    SimpleSaddleFn (bifunBracket F) :=
  (theorem_34_2_closed hF hcl (theorem_34_2_lower_mem hF hcl)).simpleSaddleFn
    (theorem_33_1_concaveConvex hF) hp

end Kernel

/-! ### Theorem 34.4 -/

section Thm344

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Theorem 34.4** of [rockafellar1970convex]. Let $K$ and $L$ be closed proper concave-convex
functions on $\mathbb{R}^m \times \mathbb{R}^n$. Then $K$ and $L$ are equivalent if and only if
they have the same kernel. -/
theorem theorem_34_4 (hclK : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K)
    (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    SaddleEquiv K L ↔ kernel K = kernel L :=
  saddleEquiv_iff_kernel_eq hclK hK hpK hclL hL hpL

end Thm344

/-! ### Theorem 34.5 and Corollary 34.5.1 -/

section Thm345

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Theorem 34.5** of [rockafellar1970convex], order of the closures. Let $K$ be a simple proper
concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$. Then $\operatorname{cl}_2
\operatorname{cl}_1 K \le \operatorname{cl}_1 \operatorname{cl}_2 K$. -/
theorem theorem_34_5_le (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : lowerCl K ≤ upperCl K :=
  lowerCl_le_upperCl hK hp hs

/-- **Theorem 34.5** of [rockafellar1970convex], equivalence of the closures. Let $K$ be a simple
proper concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$. Then
$\operatorname{cl}_2 \operatorname{cl}_1 K$ and $\operatorname{cl}_1 \operatorname{cl}_2 K$ are
equivalent. -/
theorem theorem_34_5_equiv (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : SaddleEquiv (lowerCl K) (upperCl K) :=
  saddleEquiv_lowerCl_upperCl hK hp hs

/-- **Theorem 34.5** of [rockafellar1970convex], closedness. Let $K$ be a simple proper
concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$. Then every $L$ with
$\operatorname{cl}_2 \operatorname{cl}_1 K \le L \le \operatorname{cl}_1 \operatorname{cl}_2 K$
is closed. -/
theorem theorem_34_5_closed (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : ClosedSaddleFn L :=
  closedSaddleFn_of_mem_saddleClass_lowerCl hK hp hs hL

/-- **Theorem 34.5** of [rockafellar1970convex], properness. Let $K$ be a proper concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$. Then every $L$ with $\operatorname{cl}_2
\operatorname{cl}_1 K \le L \le \operatorname{cl}_1 \operatorname{cl}_2 K$ is proper. -/
theorem theorem_34_5_proper (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : ProperSaddleFn L :=
  properSaddleFn_of_mem_saddleClass_lowerCl hK hp hL

/-- **Theorem 34.5** of [rockafellar1970convex], the kernel. Let $K$ be a simple proper
concave-convex function on $\mathbb{R}^m \times \mathbb{R}^n$. Then every concave-convex $L$
with $\operatorname{cl}_2 \operatorname{cl}_1 K \le L \le \operatorname{cl}_1
\operatorname{cl}_2 K$ has the same kernel as $K$. -/
theorem theorem_34_5_kernel (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hL : ConcaveConvexFn L)
    (hmem : L ∈ saddleClass (lowerCl K) (upperCl K)) : kernel L = kernel K :=
  kernel_of_mem_saddleClass_lowerCl hK hp hs hL hmem

/-- **Theorem 34.5** of [rockafellar1970convex], converse. Let $K$ be a simple proper concave-convex
function on $\mathbb{R}^m \times \mathbb{R}^n$, and let $L$ be a closed proper concave-convex
function with the same kernel as $K$. Then $\operatorname{cl}_2 \operatorname{cl}_1 K \le L \le
\operatorname{cl}_1 \operatorname{cl}_2 K$. So the interval between the two closures is the
whole equivalence class. -/
theorem theorem_34_5_mem_of_kernel_eq (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L)
    (hpL : ProperSaddleFn L) (hker : kernel L = kernel K) :
    L ∈ saddleClass (lowerCl K) (upperCl K) :=
  mem_saddleClass_lowerCl_of_kernel_eq hK hp hs hclL hL hpL hker

/-- **Theorem 34.5** of [rockafellar1970convex]. Let $K$ be a simple proper concave-convex function
on $\mathbb{R}^m \times \mathbb{R}^n$. Then the kernel of $K$ is the kernel of exactly one
equivalence class of closed proper concave-convex functions: there is a closed proper
concave-convex $M$ with the same kernel as $K$, and a closed proper concave-convex $L$ has the
same kernel as $K$ if and only if $L$ is equivalent to $M$.

The function $M$ in the proof is $\operatorname{cl}_2 \operatorname{cl}_1 K$. -/
theorem theorem_34_5 (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SimpleSaddleFn K) :
    ∃ M : Rn m × Rn n → EReal, (ClosedSaddleFn M ∧ ConcaveConvexFn M ∧ ProperSaddleFn M ∧
      kernel M = kernel K) ∧ ∀ L : Rn m × Rn n → EReal, ClosedSaddleFn L → ConcaveConvexFn L →
      ProperSaddleFn L → (kernel L = kernel K ↔ SaddleEquiv M L) :=
  exists_unique_saddleEquiv_class_of_kernel hK hp hs

end Thm345

/-! ### Corollary 34.5.1 -/

section Cor3451

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Corollary 34.5.1** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^m$ and
$D \subseteq \mathbb{R}^n$ be non-empty convex sets, and let $K : \mathbb{R}^m \times
\mathbb{R}^n \to \mathbb{R}$ be such that $K(u, \cdot)$ is convex on $D$ for each $u \in C$ and
$K(\cdot, v)$ is concave on $C$ for each $v \in D$. Then there is exactly one equivalence class
of closed proper concave-convex functions on $\mathbb{R}^m \times \mathbb{R}^n$ whose kernel is
the restriction of $K$ to $\operatorname{ri}(C \times D)$: there is a closed proper
concave-convex $M$ with this kernel, and a closed proper concave-convex $L$ has this kernel if
and only if $L$ is equivalent to $M$.

The restriction of $K$ to $\operatorname{ri}(C \times D)$ is extended by $+\infty$, as for the
kernel. The convexity of $D$ is part of the hypothesis `ConvexOn ℝ D`. -/
theorem corollary_34_5_1 (hC : Convex ℝ C) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v)) :
    ∃ M : Rn m × Rn n → EReal, (ClosedSaddleFn M ∧ ConcaveConvexFn M ∧ ProperSaddleFn M ∧
      kernel M = ConvexAnalysis.convexRestrict (ri (C ×ˢ D)) fun p => (K p : EReal)) ∧
      ∀ L : Rn m × Rn n → EReal, ClosedSaddleFn L → ConcaveConvexFn L → ProperSaddleFn L →
        (kernel L = ConvexAnalysis.convexRestrict (ri (C ×ˢ D)) (fun p => (K p : EReal)) ↔
          SaddleEquiv M L) :=
  exists_unique_saddleEquiv_class_of_finite hC hCne hDne ⟨hconc, hconv⟩

end Cor3451

end Rockafellar
