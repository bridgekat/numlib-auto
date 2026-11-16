/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Optimization.Complexity.Basic
import Numlib.Optimization.Complexity.OracleMethod

/-!
# Zero chains and zero-respecting methods

This module sets up the lower-bound framework of §4.2 of [cartis2022evaluation], which follows
Carmon, Duchi, Hinder and Sidford, *Lower bounds for finding stationary points I*. A $p$-th order
method queries, at each iterate $x_i$, the oracle that returns the jet $(f(x_i), \nabla f(x_i),
\dots, \nabla^p f(x_i))$, and chooses $x_{k+1}$ as a function of the answers at $x_0, \dots, x_k$.
For a method $M$ and a function $f$, $k_\varepsilon(M, f)$ is the index of the first iterate with
$\|\nabla f(x_k)\| \le \varepsilon$. For a class $\mathcal{M}$ of methods and a class $\mathcal{F}$
of functions of any dimension, the complexity (4.2.2) is
$$\#_\varepsilon(\mathcal{M}, \mathcal{F}) = \inf_{M \in \mathcal{M}} \sup_{f \in \mathcal{F}}
  k_\varepsilon(M, f).$$

A method is zero-respecting (4.2.1) if it starts at $0$ and leaves a coordinate $j$ of $x_{k+1}$ at
zero when no derivative seen so far is nonzero in the direction $e_j$. A function
$f : \mathbb{R}^n \to \mathbb{R}$ is a zero chain (4.2.4) if, whenever the coordinates
$j, j+1, \dots$ of $x$ vanish, the derivatives of $f$ at $x$ do not see the directions $e_i$ with
$i > j$. Then a zero-respecting method uncovers at most one new coordinate per iteration (Lemma
4.2.2). If $\|\nabla f(x)\| > \varepsilon$ whenever the last coordinate of $x$ vanishes, such a
method needs at least $n$ iterations (Lemma 4.2.3).

## Main definitions

* `Optimization.Jet`: the answers $(f(x), \nabla f(x), \dots, \nabla^p f(x))$ of the $p$-th order
  oracle.
* `Optimization.JetMethod`: a deterministic $p$-th order oracle method in every dimension, the maps
  $M^{(k)}$ of [cartis2022evaluation].
* `Optimization.methodClass`: the class $\mathcal{M}(p)$ of such methods that start at $x_0 = 0$.
* `Optimization.firstStationaryIndex`: the index $k_\varepsilon$ of the first
  $\varepsilon$-stationary point of a sequence, in $\mathbb{N} \cup \{\infty\}$.
* `Optimization.classComplexity`: the complexity $\#_\varepsilon(\mathcal{M}, \mathcal{F})$ of
  (4.2.2).
* `Optimization.smoothClass`: the class $\mathcal{F}(\Delta, p)$ of smooth functions, bounded below,
  with $L$-Lipschitz $p$-th derivative and $f(0) - \inf f \le \Delta$.
* `Optimization.IsNullDirection`: a multilinear map vanishes whenever one of its arguments is a
  given vector.
* `Optimization.IsZeroRespectingFor` and `Optimization.zeroRespectingClass`: zero-respecting methods
  (4.2.1) and the class $\mathcal{M}_{ZR}(p)$.
* `Optimization.IsZeroChain`: $p$-th order zero chains (4.2.4).

## Main results

* `Optimization.comp_adjoint_mem_smoothClass`: the class $\mathcal{F}(\Delta, p)$ is invariant under
  $f \mapsto f \circ U^T$ for a linear isometry $U$ (footnote 30).
* `Optimization.isNullDirection_iff_curryLeft_eq_zero`: for a symmetric multilinear map $A$, $v$ is
  a null direction if and only if $A[v, \cdot] = 0$.
* `Optimization.IsZeroChain.comp_smul`: zero chains are invariant under the scaling
  $x \mapsto \mu_1 f(x / \mu_2)$ (Lemma 4.2.1).
* `Optimization.IsZeroRespectingFor.iterate_apply_eq_zero`: on a zero chain, the $k$-th iterate of a
  zero-respecting method vanishes in the coordinates $j \ge k$ (Lemma 4.2.2).
* `Optimization.le_firstStationaryIndex_of_isZeroChain` and
  `Optimization.le_classComplexity_of_isZeroChain`: the lower bound $n$ on the number of iterations
  (Lemma 4.2.3).

## Implementation notes

* The spaces are `EuclideanSpace ℝ (Fin n)`, since zero chains and zero-respecting methods are
  coordinate notions. The coordinate vector $e_j$ is `EuclideanSpace.single j 1`.
* Coordinates are $0$-based: the coordinate $[x]_j$ with $j \in [1 : n]$ of [cartis2022evaluation]
  is `x ⟨j - 1, _⟩`.
* The source writes $\nabla^q f(x) e_j = 0$. Here this is `Optimization.IsNullDirection` for $e_j$,
  which agrees with it for symmetric tensors (`Optimization.isNullDirection_iff_curryLeft_eq_zero`).
* A class of functions of variable dimension is a set of pairs $(n, f)$ with
  $f : \mathbb{R}^n \to \mathbb{R}$, that is, a set in `Σ n, EuclideanSpace ℝ (Fin n) → ℝ`.
-/

open Set Filter Topology ContDiff
open scoped InnerProductSpace

namespace Optimization

/-! ### Jets, jet methods and the class $\mathcal{M}(p)$ -/

/-- The answers of the $p$-th order oracle on a real normed space $E$: one continuous $j$-linear
form $E^j \to \mathbb{R}$ for each $j = 0, \dots, p$. For a function $f$ and a point $x$,
`Optimization.jetOracle f p x` gives the values $\nabla^j f(x)$. -/
abbrev Jet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℕ) :=
  (j : Fin (p + 1)) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ

/-- A **$p$-th order method** in every dimension: for each $n \in \mathbb{N}$, a deterministic
oracle method on $\mathbb{R}^n$ whose next iterate $x_{k+1}$ is a function of the jets $(f(x_i),
\nabla f(x_i), \dots, \nabla^p f(x_i))$ at the previous iterates $x_i$, $i \le k$. These are the
maps $M^{(k)}$ of §4.2.1.2 of [cartis2022evaluation].

For each $n$ the method is an `Optimization.OracleMethod` on `EuclideanSpace ℝ (Fin n)` whose
oracle answers are `Optimization.Jet`s. -/
abbrev JetMethod (p : ℕ) :=
  (n : ℕ) → OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) p)

namespace JetMethod

variable {p : ℕ}

/-- The $k$-th iterate $x_k$ of the method $M$ applied to $f : \mathbb{R}^n \to \mathbb{R}$, with
the $p$-th order oracle of $f$. -/
noncomputable def iter (M : JetMethod p) (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (M n).iterate (jetOracle f p) k

/-- The iterates of $M$ on $f$ are the iterates of the oracle method $M_n$ with the oracle
`Optimization.jetOracle f p`. -/
theorem iter_eq (M : JetMethod p) (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    M.iter n f = (M n).iterate (jetOracle f p) := rfl

end JetMethod

/-- The class $\mathcal{M}(p)$ of $p$-th order methods of §4.2.1.2 of [cartis2022evaluation]: the
jet methods whose initial point is $x_0 = 0$ in every dimension. -/
def methodClass (p : ℕ) : Set (JetMethod p) := {M | ∀ n, (M n).x₀ = 0}

/-- $M \in \mathcal{M}(p)$ if and only if the initial point of $M$ is $0$ in every dimension. -/
theorem mem_methodClass {p : ℕ} {M : JetMethod p} : M ∈ methodClass p ↔ ∀ n, (M n).x₀ = 0 :=
  Iff.rfl

/-! ### The first $\varepsilon$-stationary iterate -/

section FirstStationary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $(x_k)$ be a sequence in a real normed space $E$, $f : E \to \mathbb{R}$ and
$\varepsilon \in \mathbb{R}$. The **index of the first $\varepsilon$-stationary point** is the
least $k$ with $\|\nabla f(x_k)\| \le \varepsilon$, as an element of
$\mathbb{N} \cup \{\infty\}$, and it is $\infty$ if no point of the sequence is
$\varepsilon$-stationary. When $(x_k)$ is the sequence of iterates of a method $M$ on $f$, this
is $k_\varepsilon(M, f)$ of §4.2.1.3 of [cartis2022evaluation].

The norm is that of `fderiv ℝ f (x k)`. Where $f$ is not differentiable, `fderiv ℝ f` is zero,
so such points count as stationary when $\varepsilon \ge 0$; all functions of
`Optimization.smoothClass` are differentiable. The value lies in `ℕ∞`, whose top element is
$\infty$. -/
noncomputable def firstStationaryIndex (x : ℕ → E) (f : E → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ‖fderiv ℝ f (x k)‖ ≤ ε), (k : ℕ∞)

variable {x : ℕ → E} {f : E → ℝ} {ε : ℝ}

/-- For $c \in \mathbb{N} \cup \{\infty\}$, $c \le k_\varepsilon$ if and only if
$\|\nabla f(x_k)\| > \varepsilon$ for every $k < c$. -/
theorem le_firstStationaryIndex_iff {c : ℕ∞} :
    c ≤ firstStationaryIndex x f ε ↔ ∀ k : ℕ, (k : ℕ∞) < c → ε < ‖fderiv ℝ f (x k)‖ := by
  simp only [firstStationaryIndex, le_iInf_iff]
  constructor
  · intro h k hk
    by_contra hle
    exact absurd (h k (not_lt.1 hle)) (not_le.2 hk)
  · intro h k hk
    by_contra hlt
    exact absurd hk (not_le.2 (h k (not_le.1 hlt)))

/-- For $c \in \mathbb{N}$, $c \le k_\varepsilon$ if and only if $\|\nabla f(x_k)\| > \varepsilon$
for every $k < c$. -/
theorem coe_le_firstStationaryIndex_iff {c : ℕ} :
    (c : ℕ∞) ≤ firstStationaryIndex x f ε ↔ ∀ k < c, ε < ‖fderiv ℝ f (x k)‖ := by
  rw [le_firstStationaryIndex_iff]
  exact forall_congr' fun k => by rw [Nat.cast_lt]

/-- If $\|\nabla f(x_k)\| \le \varepsilon$, then $k_\varepsilon \le k$. -/
theorem firstStationaryIndex_le {k : ℕ} (hk : ‖fderiv ℝ f (x k)‖ ≤ ε) :
    firstStationaryIndex x f ε ≤ k :=
  iInf₂_le k hk

/-- $k_\varepsilon = \infty$ if and only if $\|\nabla f(x_k)\| > \varepsilon$ for every $k$. -/
theorem firstStationaryIndex_eq_top_iff :
    firstStationaryIndex x f ε = ⊤ ↔ ∀ k, ε < ‖fderiv ℝ f (x k)‖ := by
  rw [← top_le_iff, le_firstStationaryIndex_iff]
  exact forall_congr' fun k => by simp

/-- For $k \in \mathbb{N}$, $k_\varepsilon = k$ if and only if $x_k$ is the first
$\varepsilon$-stationary point of the sequence: $\|\nabla f(x_k)\| \le \varepsilon$ and
$\|\nabla f(x_j)\| > \varepsilon$ for all $j < k$. -/
theorem firstStationaryIndex_eq_coe_iff {k : ℕ} :
    firstStationaryIndex x f ε = k ↔ IsFirstHit (fun j => ‖fderiv ℝ f (x j)‖ ≤ ε) k := by
  constructor
  · intro h
    have hle := (coe_le_firstStationaryIndex_iff (x := x) (f := f) (ε := ε) (c := k)).1 h.ge
    refine ⟨?_, fun j hj => not_le.2 (hle j hj)⟩
    by_contra hk
    have : ((k + 1 : ℕ) : ℕ∞) ≤ firstStationaryIndex x f ε := by
      rw [coe_le_firstStationaryIndex_iff]
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hle j hj
      · exact not_le.1 hk
    rw [h] at this
    exact absurd (Nat.cast_le.1 this) (by omega)
  · intro h
    refine le_antisymm (firstStationaryIndex_le h.test) ?_
    rw [coe_le_firstStationaryIndex_iff]
    exact fun j hj => not_le.1 (h.not_test_of_lt hj)

/-- Let $(x_k)$ be a sequence in $E$ with $f : E \to \mathbb{R}$, let $(y_k)$ be a sequence in a
real normed space $F$ with $g : F \to \mathbb{R}$, and let $T \in \mathbb{N}$ and
$\varepsilon \in \mathbb{R}$. If, for every $k < T$, $\|\nabla f(x_k)\| \le \varepsilon$ implies
$\|\nabla g(y_k)\| \le \varepsilon$, then
$$\min\bigl(T, k_\varepsilon(y, g)\bigr) \le k_\varepsilon(x, f).$$

The two sequences may live in different spaces. This is used to transfer a lower bound on
$k_\varepsilon$ from one function to another. -/
theorem min_firstStationaryIndex_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {y : ℕ → F} {g : F → ℝ} {T : ℕ}
    (h : ∀ k < T, ‖fderiv ℝ f (x k)‖ ≤ ε → ‖fderiv ℝ g (y k)‖ ≤ ε) :
    min (T : ℕ∞) (firstStationaryIndex y g ε) ≤ firstStationaryIndex x f ε := by
  rw [le_firstStationaryIndex_iff]
  intro k hk
  rw [lt_min_iff] at hk
  by_contra hle
  have := h k (Nat.cast_lt.1 hk.1) (not_lt.1 hle)
  exact absurd (firstStationaryIndex_le (x := y) this) (not_le.2 hk.2)

end FirstStationary

/-! ### The complexity of a class of methods on a class of functions -/

section Complexity

variable {p : ℕ}

/-- Let $\mathcal{M}$ be a set of $p$-th order methods, $\mathcal{F}$ a set of functions
$f : \mathbb{R}^n \to \mathbb{R}$ of variable dimension $n$, and $\varepsilon \in \mathbb{R}$.
The **complexity** of $\mathcal{M}$ on $\mathcal{F}$ is
$$\#_\varepsilon(\mathcal{M}, \mathcal{F}) = \inf_{M \in \mathcal{M}} \sup_{f \in \mathcal{F}}
  k_\varepsilon(M, f) \in \mathbb{N} \cup \{\infty\},$$
where $k_\varepsilon(M, f)$ is the index of the first $\varepsilon$-stationary iterate of $M$ on
$f$. This is (4.2.2) of [cartis2022evaluation].

A function of $\mathcal{F}$ is a pair `F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ` of a dimension and
a function. The infimum and the supremum are taken in `ℕ∞`: an empty $\mathcal{M}$ gives
$\infty$, and an empty $\mathcal{F}$ gives $0$. -/
noncomputable def classComplexity (𝓜 : Set (JetMethod p))
    (𝓕 : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)) (ε : ℝ) : ℕ∞ :=
  ⨅ M ∈ 𝓜, ⨆ F ∈ 𝓕, firstStationaryIndex (M.iter F.1 F.2) F.2 ε

variable {𝓜 𝓜' : Set (JetMethod p)} {𝓕 𝓕' : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)} {ε : ℝ}

/-- $c \le \#_\varepsilon(\mathcal{M}, \mathcal{F})$ if and only if $c \le \sup_{f \in \mathcal{F}}
k_\varepsilon(M, f)$ for every $M \in \mathcal{M}$. -/
theorem le_classComplexity_iff {c : ℕ∞} :
    c ≤ classComplexity 𝓜 𝓕 ε ↔
      ∀ M ∈ 𝓜, c ≤ ⨆ F ∈ 𝓕, firstStationaryIndex (M.iter F.1 F.2) F.2 ε := by
  simp only [classComplexity, le_iInf_iff]

/-- $c \le \#_\varepsilon(\mathcal{M}, \mathcal{F})$ if and only if for every method
$M \in \mathcal{M}$ and every $k < c$ some $f \in \mathcal{F}$ has $k < k_\varepsilon(M, f)$. No
function needs to attain the supremum. -/
theorem le_classComplexity_iff_forall_lt {c : ℕ∞} :
    c ≤ classComplexity 𝓜 𝓕 ε ↔
      ∀ M ∈ 𝓜, ∀ k < c, ∃ F ∈ 𝓕, k < firstStationaryIndex (M.iter F.1 F.2) F.2 ε := by
  rw [le_classComplexity_iff]
  refine forall₂_congr fun M _ => ?_
  constructor
  · intro h k hk
    have := hk.trans_le h
    simpa only [lt_iSup_iff, exists_prop] using this
  · intro h
    refine le_of_forall_lt fun k hk => ?_
    obtain ⟨F, hF, hk⟩ := h k hk
    exact hk.trans_le (le_iSup₂ (f := fun F (_ : F ∈ 𝓕) =>
      firstStationaryIndex (M.iter F.1 F.2) F.2 ε) F hF)

/-- If for every method $M \in \mathcal{M}$ some $f \in \mathcal{F}$ has
$c \le k_\varepsilon(M, f)$, then $c \le \#_\varepsilon(\mathcal{M}, \mathcal{F})$. -/
theorem le_classComplexity_of_forall_exists {c : ℕ∞}
    (h : ∀ M ∈ 𝓜, ∃ F ∈ 𝓕, c ≤ firstStationaryIndex (M.iter F.1 F.2) F.2 ε) :
    c ≤ classComplexity 𝓜 𝓕 ε := by
  rw [le_classComplexity_iff]
  intro M hM
  obtain ⟨F, hF, hc⟩ := h M hM
  exact hc.trans (le_iSup₂ (f := fun F (_ : F ∈ 𝓕) =>
    firstStationaryIndex (M.iter F.1 F.2) F.2 ε) F hF)

/-- For a single function $f$, $c \le \#_\varepsilon(\mathcal{M}, \{f\})$ if and only if
$c \le k_\varepsilon(M, f)$ for every $M \in \mathcal{M}$. -/
theorem le_classComplexity_singleton_iff {c : ℕ∞} {F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ} :
    c ≤ classComplexity 𝓜 {F} ε ↔ ∀ M ∈ 𝓜, c ≤ firstStationaryIndex (M.iter F.1 F.2) F.2 ε := by
  simp only [le_classComplexity_iff, mem_singleton_iff, iSup_iSup_eq_left]

/-- The complexity decreases when the class of methods grows: if
$\mathcal{M} \subseteq \mathcal{M}'$, then $\#_\varepsilon(\mathcal{M}', \mathcal{F}) \le
\#_\varepsilon(\mathcal{M}, \mathcal{F})$. -/
theorem classComplexity_anti_left (h : 𝓜 ⊆ 𝓜') :
    classComplexity 𝓜' 𝓕 ε ≤ classComplexity 𝓜 𝓕 ε :=
  biInf_mono h

/-- The complexity increases when the class of functions grows: if
$\mathcal{F} \subseteq \mathcal{F}'$, then $\#_\varepsilon(\mathcal{M}, \mathcal{F}) \le
\#_\varepsilon(\mathcal{M}, \mathcal{F}')$. -/
theorem classComplexity_mono_right (h : 𝓕 ⊆ 𝓕') :
    classComplexity 𝓜 𝓕 ε ≤ classComplexity 𝓜 𝓕' ε :=
  iInf₂_mono fun _ _ => biSup_mono h

end Complexity

/-! ### Orthogonal embeddings and the class $\mathcal{F}(\Delta, p)$ -/

section Embedding

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Let $E$ and $F$ be real Hilbert spaces and $U : E \to F$ a linear isometry. The **adjoint**
$U^T : F \to E$ is the continuous linear map with $\langle U^T z, x \rangle = \langle z, U x
\rangle$. For $U \in O(\bar n, n)$, a matrix with orthonormal columns, this is the transpose
$U^T$ of [cartis2022evaluation].

The definition is `ContinuousLinearMap.adjoint` of `U.toContinuousLinearMap`. -/
noncomputable def isometryAdjoint (U : E →ₗᵢ[ℝ] F) : F →L[ℝ] E :=
  ContinuousLinearMap.adjoint U.toContinuousLinearMap

variable (U : E →ₗᵢ[ℝ] F)

/-- The adjoint satisfies $\langle U^T z, x \rangle = \langle z, U x \rangle$ for all $z \in F$ and
$x \in E$. -/
theorem inner_isometryAdjoint_apply (z : F) (x : E) :
    ⟪isometryAdjoint U z, x⟫_ℝ = ⟪z, U x⟫_ℝ := by
  rw [isometryAdjoint, ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- $U^T U = I$: $U^T(U x) = x$ for all $x \in E$. -/
@[simp]
theorem isometryAdjoint_apply_self (x : E) : isometryAdjoint U (U x) = x := by
  refine ext_inner_right ℝ fun y => ?_
  rw [inner_isometryAdjoint_apply, U.inner_map_map]

/-- The adjoint $U^T$ of a linear isometry is surjective. -/
theorem isometryAdjoint_surjective : Function.Surjective (isometryAdjoint U) :=
  fun x => ⟨U x, isometryAdjoint_apply_self U x⟩

/-- The adjoint $U^T$ of a linear isometry has operator norm at most $1$. -/
theorem norm_isometryAdjoint_le : ‖isometryAdjoint U‖ ≤ 1 := by
  rw [isometryAdjoint, ContinuousLinearMap.adjoint.norm_map]
  exact U.norm_toContinuousLinearMap_le

/-- $\|U^T z\| \le \|z\|$ for all $z \in F$. -/
theorem norm_isometryAdjoint_apply_le (z : F) : ‖isometryAdjoint U z‖ ≤ ‖z‖ :=
  by simpa using (isometryAdjoint U).le_of_opNorm_le (norm_isometryAdjoint_le U) z

/-- For a continuous $q$-linear form $A$ on $E$, the form $A[U^T \cdot, \dots, U^T \cdot]$ on $F$
has the same norm as $A$. -/
theorem norm_compContinuousLinearMap_isometryAdjoint {q : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) :
    ‖A.compContinuousLinearMap fun _ => isometryAdjoint U‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · refine (A.norm_compContinuousLinearMap_le _).trans ?_
    calc ‖A‖ * ∏ _ : Fin q, ‖isometryAdjoint U‖ ≤ ‖A‖ * ∏ _ : Fin q, (1 : ℝ) := by
          gcongr with i; exact norm_isometryAdjoint_le U
      _ = ‖A‖ := by simp
  · refine A.opNorm_le_bound (norm_nonneg _) fun v => ?_
    have h := (A.compContinuousLinearMap fun _ => isometryAdjoint U).le_opNorm (fun i => U (v i))
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      isometryAdjoint_apply_self, LinearIsometry.norm_map] at h
    exact h

/-- Let $f : E \to \mathbb{R}$ be $N$ times continuously differentiable and $q \le N$. Then the
derivatives of $f \circ U^T$ are those of $f$ composed with $U^T$ in every argument:
$$\nabla^q (f \circ U^T)(z) = \nabla^q f(U^T z)[U^T \cdot, \dots, U^T \cdot].$$
-/
theorem iteratedFDeriv_comp_isometryAdjoint {f : E → ℝ} {N : WithTop ℕ∞} (hf : ContDiff ℝ N f)
    {q : ℕ} (hq : (q : WithTop ℕ∞) ≤ N) (z : F) :
    iteratedFDeriv ℝ q (f ∘ isometryAdjoint U) z =
      (iteratedFDeriv ℝ q f (isometryAdjoint U z)).compContinuousLinearMap
        fun _ => isometryAdjoint U :=
  (isometryAdjoint U).iteratedFDeriv_comp_right hf z hq

/-- Let $f : E \to \mathbb{R}$ be $N$ times continuously differentiable and $q \le N$. Then
$\|\nabla^q (f \circ U^T)(z)\| = \|\nabla^q f(U^T z)\|$ for all $z \in F$. -/
theorem norm_iteratedFDeriv_comp_isometryAdjoint {f : E → ℝ} {N : WithTop ℕ∞}
    (hf : ContDiff ℝ N f) {q : ℕ} (hq : (q : WithTop ℕ∞) ≤ N) (z : F) :
    ‖iteratedFDeriv ℝ q (f ∘ isometryAdjoint U) z‖ =
      ‖iteratedFDeriv ℝ q f (isometryAdjoint U z)‖ := by
  rw [iteratedFDeriv_comp_isometryAdjoint U hf hq, norm_compContinuousLinearMap_isometryAdjoint]

/-- If $f$ is differentiable at $U^T z$, then $\|\nabla(f \circ U^T)(z)\| = \|\nabla f(U^T z)\|$. -/
theorem norm_fderiv_comp_isometryAdjoint {f : E → ℝ} (z : F)
    (hf : DifferentiableAt ℝ f (isometryAdjoint U z)) :
    ‖fderiv ℝ (f ∘ isometryAdjoint U) z‖ = ‖fderiv ℝ f (isometryAdjoint U z)‖ := by
  rw [fderiv_comp z hf (isometryAdjoint U).differentiableAt, ContinuousLinearMap.fderiv]
  refine le_antisymm ?_ ?_
  · calc ‖(fderiv ℝ f (isometryAdjoint U z)).comp (isometryAdjoint U)‖
        ≤ ‖fderiv ℝ f (isometryAdjoint U z)‖ * ‖isometryAdjoint U‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ f (isometryAdjoint U z)‖ * 1 := by
          gcongr; exact norm_isometryAdjoint_le U
      _ = _ := mul_one _
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h := ((fderiv ℝ f (isometryAdjoint U z)).comp (isometryAdjoint U)).le_opNorm (U x)
    simpa only [ContinuousLinearMap.comp_apply, isometryAdjoint_apply_self,
      LinearIsometry.norm_map] using h

/-- The range of $f \circ U^T$ is the range of $f$, since $U^T$ is surjective. -/
theorem range_comp_isometryAdjoint (f : E → ℝ) : range (f ∘ isometryAdjoint U) = range f :=
  (isometryAdjoint_surjective U).range_comp f

end Embedding

/-- Composition with a fixed linear map in every argument commutes with subtraction of multilinear
maps. -/
private theorem sub_compContinuousLinearMap {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {q : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (g : G →L[ℝ] E) :
    (A - B).compContinuousLinearMap (fun _ => g) =
      A.compContinuousLinearMap (fun _ => g) - B.compContinuousLinearMap (fun _ => g) := by
  ext v; simp

/-- Let $\Delta, L \in \mathbb{R}$ and $p \in \mathbb{N}$. The class **$\mathcal{F}(\Delta, p)$** of
§4.2.1.1 of [cartis2022evaluation], with the Lipschitz constant $L$ of the $p$-th derivative
made explicit, consists of the functions $f : \mathbb{R}^n \to \mathbb{R}$, of any dimension
$n$, such that

* $f$ is infinitely differentiable (footnote 29 of the source);
* $\nabla^p f$ is Lipschitz with constant $L$ on $\mathbb{R}^n$ (assumption f.DpL);
* $f$ is bounded below (assumption f.Bb);
* $f(0) - \inf f \le \Delta$.

An element is a pair `F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ`. The Lipschitz condition is
`IteratedFDerivLipschitzOn F.2 p L univ`. The infimum of $f$ is `⨅ x, F.2 x`. -/
def smoothClass (Δ L : ℝ) (p : ℕ) : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ) :=
  {F | ContDiff ℝ ∞ F.2 ∧ IteratedFDerivLipschitzOn F.2 p L univ ∧ BddBelow (range F.2) ∧
    F.2 0 - ⨅ x, F.2 x ≤ Δ}

/-- $(n, f) \in \mathcal{F}(\Delta, p)$ if and only if $f$ is infinitely differentiable,
$\nabla^p f$ is $L$-Lipschitz on $\mathbb{R}^n$, $f$ is bounded below, and
$f(0) - \inf f \le \Delta$. -/
theorem mem_smoothClass {Δ L : ℝ} {p : ℕ} {F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ} :
    F ∈ smoothClass Δ L p ↔ ContDiff ℝ ∞ F.2 ∧ IteratedFDerivLipschitzOn F.2 p L univ ∧
      BddBelow (range F.2) ∧ F.2 0 - ⨅ x, F.2 x ≤ Δ :=
  Iff.rfl

/-- **Orthogonal invariance of $\mathcal{F}(\Delta, p)$**, §4.2.1.1 of [cartis2022evaluation],
footnote 30. Let $L \ge 0$, let $f : \mathbb{R}^n \to \mathbb{R}$ belong to
$\mathcal{F}(\Delta, p)$ with Lipschitz constant $L$, and let
$U : \mathbb{R}^n \to \mathbb{R}^m$ be a linear isometry, that is, an $m \times n$ matrix with
orthonormal columns. Then $f_U = f \circ U^T : \mathbb{R}^m \to \mathbb{R}$ belongs to
$\mathcal{F}(\Delta, p)$ with the same constants.

The hypothesis $L \ge 0$ is needed: for $L < 0$ the class contains only functions on
$\mathbb{R}^0$. The map $U^T$ is `Optimization.isometryAdjoint U`. -/
theorem comp_adjoint_mem_smoothClass {Δ L : ℝ} {p n m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hL0 : 0 ≤ L)
    (hf : (⟨n, f⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ) ∈ smoothClass Δ L p)
    (U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    (⟨m, f ∘ isometryAdjoint U⟩ : Σ n, EuclideanSpace ℝ (Fin n) → ℝ) ∈ smoothClass Δ L p := by
  obtain ⟨hc, hL, hb, hΔ⟩ := hf
  refine ⟨hc.comp (isometryAdjoint U).contDiff, ?_, ?_, ?_⟩
  · intro z _ w _
    dsimp only
    rw [iteratedFDeriv_comp_isometryAdjoint U hc (by exact_mod_cast le_top),
      iteratedFDeriv_comp_isometryAdjoint U hc (by exact_mod_cast le_top),
      ← sub_compContinuousLinearMap,
      norm_compContinuousLinearMap_isometryAdjoint]
    refine (hL _ trivial _ trivial).trans ?_
    rw [Real.rpow_one, Real.rpow_one, ← map_sub]
    exact mul_le_mul_of_nonneg_left (norm_isometryAdjoint_apply_le U _) hL0
  · dsimp only
    rwa [range_comp_isometryAdjoint]
  · dsimp only
    have h1 : (⨅ x, (f ∘ isometryAdjoint U) x) = ⨅ x, f x := by
      rw [← sInf_range, ← sInf_range, range_comp_isometryAdjoint]
    rw [h1, Function.comp_apply, map_zero]
    exact hΔ

/-! ### Null directions of multilinear maps -/

section NullDirection

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {q : ℕ}

/-- Let $A : E^q \to G$ be a continuous multilinear map and $v \in E$. Then $v$ is a **null
direction** of $A$ if $A$ vanishes whenever one of its arguments is $v$:
$$A(w_1, \dots, w_{i-1}, v, w_{i+1}, \dots, w_q) = 0 \qquad \text{for all } i \text{ and all }
  w.$$
For a derivative tensor $A = \nabla^q f(x)$ and $v = e_j$, this is the condition
$\nabla^q f(x) e_j = 0$ of (4.2.1) and (4.2.4) of [cartis2022evaluation].

For symmetric $A$ the condition is $A[v, \cdot] = 0$; see
`Optimization.isNullDirection_iff_curryLeft_eq_zero`. -/
def IsNullDirection (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G) (v : E) : Prop :=
  ∀ (i : Fin q) (w : Fin q → E), A (Function.update w i v) = 0

variable {A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G} {v v' : E}

/-- The zero vector is a null direction of every multilinear map. -/
theorem isNullDirection_zero : IsNullDirection A 0 :=
  fun i w => A.map_update_zero w i

/-- The sum of two null directions of $A$ is a null direction of $A$. -/
theorem IsNullDirection.add (hv : IsNullDirection A v) (hv' : IsNullDirection A v') :
    IsNullDirection A (v + v') := fun i w => by
  rw [A.map_update_add, hv i w, hv' i w, add_zero]

/-- A scalar multiple of a null direction of $A$ is a null direction of $A$. -/
theorem IsNullDirection.smul (hv : IsNullDirection A v) (c : ℝ) : IsNullDirection A (c • v) :=
  fun i w => by rw [A.map_update_smul, hv i w, smul_zero]

/-- The null directions of a continuous multilinear map $A$ form a submodule of $E$. -/
def nullSubmodule (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G) : Submodule ℝ E where
  carrier := {v | IsNullDirection A v}
  add_mem' := IsNullDirection.add
  zero_mem' := isNullDirection_zero
  smul_mem' c _ hv := hv.smul c

/-- $v$ belongs to the submodule of null directions of $A$ if and only if $v$ is a null direction of
$A$. -/
@[simp]
theorem mem_nullSubmodule : v ∈ nullSubmodule A ↔ IsNullDirection A v := Iff.rfl

/-- Every vector in the span of a set of null directions of $A$ is a null direction of $A$. -/
theorem isNullDirection_of_mem_span {S : Set E} (hS : ∀ u ∈ S, IsNullDirection A u)
    (hv : v ∈ Submodule.span ℝ S) : IsNullDirection A v := by
  have : Submodule.span ℝ S ≤ nullSubmodule A := Submodule.span_le.2 hS
  exact this hv

/-- If $w_i - u_i$ is a null direction of $A$ for every argument $i$, then $A(w) = A(u)$. -/
theorem apply_eq_of_forall_sub_isNullDirection {u w : Fin q → E}
    (h : ∀ i, IsNullDirection A (w i - u i)) : A w = A u := by
  classical
  suffices ∀ s : Finset (Fin q), A (s.piecewise w u) = A u by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.piecewise_insert]
    have hsi : s.piecewise w u i = u i := Finset.piecewise_eq_of_notMem _ _ _ hi
    have hw : w i = s.piecewise w u i + (w i - u i) := by rw [hsi]; abel
    rw [hw, A.map_update_add, Function.update_eq_self, h i, add_zero, ih]

/-- If $v$ is a null direction of a $(q+1)$-linear map $A$, then $A[v, \cdot] = 0$, that is,
`A.curryLeft v = 0`. -/
theorem IsNullDirection.curryLeft_eq_zero
    {A : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => E) G} (hv : IsNullDirection A v) :
    A.curryLeft v = 0 := by
  ext w
  have := hv 0 (Fin.cons v w)
  rwa [Fin.update_cons_zero, ← ContinuousMultilinearMap.curryLeft_apply] at this

/-- Let $A : E^{q+1} \to G$ be a continuous multilinear map that is symmetric, that is, invariant
under every permutation of its arguments, as a derivative tensor $\nabla^{q+1} f(x)$ is. Then
$v$ is a null direction of $A$ if and only if
$$A[v, \cdot, \dots, \cdot] = 0,$$
which is the condition $\nabla^{q+1} f(x) v = 0$ of [cartis2022evaluation].

The map $A[v, \cdot, \dots, \cdot]$ is `A.curryLeft v`. -/
theorem isNullDirection_iff_curryLeft_eq_zero
    {A : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => E) G}
    (hA : ∀ (σ : Equiv.Perm (Fin (q + 1))) (w : Fin (q + 1) → E), A (w ∘ σ) = A w) :
    IsNullDirection A v ↔ A.curryLeft v = 0 := by
  refine ⟨IsNullDirection.curryLeft_eq_zero, fun h i w => ?_⟩
  have h1 : (Function.update w i v) ∘ Equiv.swap 0 i =
      Fin.cons v (Fin.tail ((Function.update w i v) ∘ Equiv.swap 0 i)) := by
    rw [← Fin.cons_self_tail ((Function.update w i v) ∘ Equiv.swap 0 i)]
    congr 1
    simp
  rw [← hA (Equiv.swap 0 i), h1, ← ContinuousMultilinearMap.curryLeft_apply, h]
  rfl

/-- Let $g : F \to E$ be continuous linear. If $g(v)$ is a null direction of $A$, then $v$ is a null
direction of $A[g \cdot, \dots, g \cdot]$. -/
theorem IsNullDirection.compContinuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : F →L[ℝ] E} {v : F} (hv : IsNullDirection A (g v)) :
    IsNullDirection (A.compContinuousLinearMap fun _ => g) v := fun i w => by
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have : (fun j => g (Function.update w i v j)) = Function.update (fun j => g (w j)) i (g v) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [this]
  exact hv i _

/-- Let $f : E \to G$ be $N$ times continuously differentiable, $q \le N$, and let $\pi : E \to E$
be continuous linear with $\pi v = 0$. If $f = f \circ \pi$ in a neighbourhood of $x$, so that
$f$ does not depend on the $v$-component near $x$, then $v$ is a null direction of
$\nabla^q f(x)$. -/
theorem isNullDirection_iteratedFDeriv_of_eventuallyEq_comp {f : E → G} {N : WithTop ℕ∞}
    (hf : ContDiff ℝ N f) {x : E} {π : E →L[ℝ] E} (hfx : f =ᶠ[𝓝 x] f ∘ π) (hv : π v = 0)
    (hq : (q : WithTop ℕ∞) ≤ N) : IsNullDirection (iteratedFDeriv ℝ q f x) v := by
  rw [(hfx.iteratedFDeriv ℝ q).eq_of_nhds, π.iteratedFDeriv_comp_right hf x hq]
  refine IsNullDirection.compContinuousLinearMap ?_
  rw [hv]
  exact isNullDirection_zero

end NullDirection

/-! ### Zero-respecting methods -/

section ZeroRespecting

variable {n p : ℕ}

/-- Let $M$ be a $p$-th order oracle method on $\mathbb{R}^n$ with iterates $x_k$ on
$f : \mathbb{R}^n \to \mathbb{R}$. The method is **zero-respecting** for $f$, as in (4.2.1) of
[cartis2022evaluation], if

* it starts at $x_0 = 0$, and
* for all $k$ and every coordinate $j$: if, for every order $q \in [1 : p]$ and every past
  iterate $x_i$ with $i \le k$, the coordinate vector $e_j$ is a null direction of
  $\nabla^q f(x_i)$, then $[x_{k+1}]_j = 0$.

For functions of class $C^p$ the derivative tensors are symmetric, and the premise is the
condition $\nabla^q f(x_i) e_j = 0$ of the source
(`Optimization.isNullDirection_iff_curryLeft_eq_zero`). In general, "$e_j$ is a null direction
of $\nabla^q f(x_i)$" implies $\nabla^q f(x_i) e_j = 0$. So the premise here is stronger and the
requirement on the method is weaker: every method that is zero-respecting in the sense of the
source is zero-respecting here. Hence `Optimization.zeroRespectingClass p` contains
$\mathcal{M}_{ZR}(p)$ of the source, and a lower bound on $\#_\varepsilon$ for
`Optimization.zeroRespectingClass p` implies the same lower bound for $\mathcal{M}_{ZR}(p)$. -/
structure IsZeroRespectingFor
    (M : OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) p))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  /-- The initial point is the origin: $x_0 = 0$. -/
  x₀_eq_zero : M.x₀ = 0
  /-- Coordinates on which no derivative of order $1, \dots, p$ has been seen stay zero: if $e_j$ is
  a null direction of $\nabla^q f(x_i)$ for all $q \in [1 : p]$ and $i \le k$, then
  $[x_{k+1}]_j = 0$. -/
  iterate_succ_apply_eq_zero : ∀ (k : ℕ) (j : Fin n),
    (∀ q, 1 ≤ q → q ≤ p → ∀ i ≤ k, IsNullDirection
      (iteratedFDeriv ℝ q f (M.iterate (jetOracle f p) i)) (EuclideanSpace.single j 1)) →
    M.iterate (jetOracle f p) (k + 1) j = 0

/-- The class $\mathcal{M}_{ZR}(p)$ of zero-respecting $p$-th order methods of §4.2.1.2 of
[cartis2022evaluation]: the methods that are zero-respecting for every function in every
dimension. -/
def zeroRespectingClass (p : ℕ) : Set (JetMethod p) :=
  {M | ∀ n f, IsZeroRespectingFor (M n) f}

/-- $M \in \mathcal{M}_{ZR}(p)$ if and only if $M$ is zero-respecting for every
$f : \mathbb{R}^n \to \mathbb{R}$ in every dimension $n$. -/
theorem mem_zeroRespectingClass {M : JetMethod p} :
    M ∈ zeroRespectingClass p ↔ ∀ n f, IsZeroRespectingFor (M n) f := Iff.rfl

/-- Every zero-respecting method starts at $0$: $\mathcal{M}_{ZR}(p) \subseteq \mathcal{M}(p)$. -/
theorem zeroRespectingClass_subset_methodClass : zeroRespectingClass p ⊆ methodClass p :=
  fun _ hM n => (hM n 0).x₀_eq_zero

/-- The class $\mathcal{M}_{ZR}(p)$ is nonempty: the method that stays at $0$ is zero-respecting.

So the infimum in $\#_\varepsilon(\mathcal{M}_{ZR}(p), \mathcal{F})$ is not over an empty set. -/
theorem zeroRespectingClass_nonempty : (zeroRespectingClass p).Nonempty :=
  ⟨fun _ => ⟨0, fun _ _ => 0⟩, fun _ _ =>
    ⟨rfl, fun k j _ => by rw [OracleMethod.iterate_succ]; rfl⟩⟩

/-- The class $\mathcal{M}(p)$ is nonempty.

So the infimum in $\#_\varepsilon(\mathcal{M}(p), \mathcal{F})$ is not over an empty set. -/
theorem methodClass_nonempty : (methodClass p).Nonempty :=
  zeroRespectingClass_nonempty.mono zeroRespectingClass_subset_methodClass

end ZeroRespecting

/-! ### Zero chains -/

section ZeroChain

variable {n p : ℕ}

/-- A function $f : \mathbb{R}^n \to \mathbb{R}$ is a **$p$-th order zero chain**, as in (4.2.4) of
[cartis2022evaluation], if for every $x \in \mathbb{R}^n$ and every $j \in \mathbb{N}$ the
following holds: if $x_i = 0$ for all $i \ge j$, then for every order $q \in [1 : p]$ and every
$i > j$ the coordinate vector $e_i$ is a null direction of $\nabla^q f(x)$.

Coordinates are $0$-based. -/
def IsZeroChain (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin n)) (j : ℕ), (∀ i : Fin n, j ≤ i → x i = 0) →
    ∀ q, 1 ≤ q → q ≤ p → ∀ i : Fin n, j < i →
      IsNullDirection (iteratedFDeriv ℝ q f x) (EuclideanSpace.single i 1)

/-- **Lemma 4.2.1** of [cartis2022evaluation] (scale invariance of zero chains). Let
$f : \mathbb{R}^n \to \mathbb{R}$ be a $p$-th order zero chain, $\mu_1 \in \mathbb{R}$ and
$\mu_2 \neq 0$. Then
$$x \mapsto \mu_1 f(x / \mu_2)$$
is a $p$-th order zero chain. -/
theorem IsZeroChain.comp_smul {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsZeroChain f p)
    (μ₁ : ℝ) {μ₂ : ℝ} (hμ₂ : μ₂ ≠ 0) : IsZeroChain (fun x => μ₁ * f (μ₂⁻¹ • x)) p := by
  intro x j hx q hq1 hqp i hji
  -- the dilation as a continuous linear equivalence
  let g : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 μ₂⁻¹ (inv_ne_zero hμ₂))
  have hg : ∀ y, g y = μ₂⁻¹ • y := fun y => rfl
  have hfun : (fun x => μ₁ * f (μ₂⁻¹ • x)) = fun x => μ₁ • (f ∘ g) x := by
    funext y; simp [hg, smul_eq_mul]
  have hcomp : iteratedFDeriv ℝ q (f ∘ g) x =
      (iteratedFDeriv ℝ q f (g x)).compContinuousLinearMap fun _ => (g : _ →L[ℝ] _) := by
    simpa [iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) q
  have hnull : IsNullDirection (iteratedFDeriv ℝ q (f ∘ g) x) (EuclideanSpace.single i 1) := by
    rw [hcomp]
    refine IsNullDirection.compContinuousLinearMap ?_
    have h1 : (g : _ →L[ℝ] _) (EuclideanSpace.single i (1 : ℝ)) =
        μ₂⁻¹ • EuclideanSpace.single i (1 : ℝ) := hg _
    rw [h1]
    refine (hf (g x) j (fun i' hi' => ?_) q hq1 hqp i hji).smul _
    rw [hg, PiLp.smul_apply, hx i' hi', smul_zero]
  rw [hfun]
  by_cases hμ₁ : μ₁ = 0
  · subst hμ₁
    simp only [zero_smul]
    rw [iteratedFDeriv_fun_zero]
    intro i w
    rfl
  · let c : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 μ₁ hμ₁)
    have hc : (fun x => μ₁ • (f ∘ g) x) = c ∘ (f ∘ g) := rfl
    rw [hc, c.iteratedFDeriv_comp_left]
    intro i' w
    simp [hnull i' w]

/-- **Lemma 4.2.2** of [cartis2022evaluation], Observation 1 of Carmon, Duchi, Hinder and Sidford.
Let $M$ be a method on $\mathbb{R}^n$ that is zero-respecting for $f$, and let $f$ be a $p$-th
order zero chain. Then the iterates satisfy
$$[x_k]_j = 0 \qquad \text{for all coordinates } j \ge k.$$

Coordinates are $0$-based; the source writes $j \in [k + 1 : n]$. -/
theorem IsZeroRespectingFor.iterate_apply_eq_zero
    {M : OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) p)}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hM : IsZeroRespectingFor M f) (hf : IsZeroChain f p)
    (k : ℕ) (j : Fin n) (hkj : k ≤ j) : M.iterate (jetOracle f p) k j = 0 := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    rcases k with _ | k
    · simp [hM.x₀_eq_zero]
    · refine hM.iterate_succ_apply_eq_zero k j fun q hq1 hqp i hik => ?_
      exact hf _ i (fun i' hi' => ih i (by omega) i' hi') q hq1 hqp j (by omega)

/-- **Lemma 4.2.3** of [cartis2022evaluation] for one method, Observation 2 of Carmon, Duchi, Hinder
and Sidford. Let $f : \mathbb{R}^n \to \mathbb{R}$ be a $p$-th order zero chain such that
$\|\nabla f(x)\| > \varepsilon$ whenever the last coordinate of $x$ vanishes, as in (4.2.5). Let
$M$ be a method on $\mathbb{R}^n$ that is zero-respecting for $f$. Then $M$ needs at least $n$
iterations to find an $\varepsilon$-stationary point:
$$n \le k_\varepsilon(M, f).$$

The last coordinate is `x ⟨n - 1, _⟩`, and the hypothesis on it is required only for $n > 0$. -/
theorem le_firstStationaryIndex_of_isZeroChain
    {M : OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) p)}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε : ℝ} (hM : IsZeroRespectingFor M f)
    (hf : IsZeroChain f p)
    (hgrad : ∀ (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)), x ⟨n - 1, by omega⟩ = 0 →
      ε < ‖fderiv ℝ f x‖) :
    (n : ℕ∞) ≤ firstStationaryIndex (M.iterate (jetOracle f p)) f ε := by
  rw [coe_le_firstStationaryIndex_iff]
  intro k hk
  exact hgrad (by omega) _ (hM.iterate_apply_eq_zero hf k _ (by simp; omega))

/-- **Lemma 4.2.3** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$ be a $p$-th
order zero chain such that $\|\nabla f(x)\| > \varepsilon$ whenever the last coordinate of $x$
vanishes, and let $\mathcal{F}$ be a class of functions that contains $f$. Then
$$\#_\varepsilon(\mathcal{M}_{ZR}(p), \{f\}) \ge n \qquad \text{and} \qquad
  \#_\varepsilon(\mathcal{M}_{ZR}(p), \mathcal{F}) \ge n,$$
with $\#_\varepsilon$ as in (4.2.2). -/
theorem le_classComplexity_of_isZeroChain {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε : ℝ}
    (hf : IsZeroChain f p)
    (hgrad : ∀ (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)), x ⟨n - 1, by omega⟩ = 0 →
      ε < ‖fderiv ℝ f x‖)
    {𝓕 : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)} (h𝓕 : ⟨n, f⟩ ∈ 𝓕) :
    (n : ℕ∞) ≤ classComplexity (zeroRespectingClass p) {⟨n, f⟩} ε ∧
      (n : ℕ∞) ≤ classComplexity (zeroRespectingClass p) 𝓕 ε := by
  have h1 : (n : ℕ∞) ≤ classComplexity (zeroRespectingClass p) {⟨n, f⟩} ε :=
    le_classComplexity_singleton_iff.2 fun M hM =>
      le_firstStationaryIndex_of_isZeroChain (hM n f) hf hgrad
  exact ⟨h1, h1.trans (classComplexity_mono_right (singleton_subset_iff.2 h𝓕))⟩

end ZeroChain

end Optimization
