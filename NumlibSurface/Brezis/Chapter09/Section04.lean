/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Elliptic.Dirichlet
import NumlibSurface.Brezis.Chapter09.Section03

/-!
# Brezis, Section 9.4: The space $W_0^{1,p}(\Omega)$

This module formalizes Section 9.4 of [brezis2011functional], on an open set
$\Omega \subseteq \mathbb{R}^N$ with Lebesgue measure. For $1 \le p < \infty$ the space
$W_0^{1,p}(\Omega)$ is the closure of $C_c^1(\Omega)$ in $W^{1,p}(\Omega)$, and
$H_0^1(\Omega) = W_0^{1,2}(\Omega)$. The section shows that $W_0^{1,p}(\mathbb{R}^N) =
W^{1,p}(\mathbb{R}^N)$ (Remark 17), that a function with compact support in $\Omega$ lies in
$W_0^{1,p}(\Omega)$ (Lemma 9.5), and that for $\Omega$ of class $C^1$ a function
$u \in W^{1,p}(\Omega) \cap C(\bar\Omega)$ lies in $W_0^{1,p}(\Omega)$ if and only if $u = 0$ on
$\Gamma = \partial\Omega$ (Theorem 9.17). Proposition 9.18 characterizes $W_0^{1,p}(\Omega)$ by the
extension by zero $\bar u$. Because the extension by zero needs no regularity of $\Omega$, the
embeddings of Section 9.3 hold on $W_0^{1,p}(\Omega)$ for every open set (Remark 20). For bounded
$\Omega$, Poincaré's inequality $\|u\|_p \le C \|\nabla u\|_p$ holds on $W_0^{1,p}(\Omega)$
(Corollary 9.19 and Remark 21). The section ends with $W_0^{m,p}(\Omega)$ (Remark 22), the dual
space $W^{-1,p'}(\Omega)$ with the inclusions $H_0^1(\Omega) \subset L^2(\Omega) \subset
H^{-1}(\Omega)$, and the representation of the elements of $W^{-1,p'}(\Omega)$ (Proposition 9.20).

The proofs specialize the backbone modules `Numlib.Analysis.Sobolev.Zero` (the extension by zero,
Theorem 9.17, Proposition 9.18, Remarks 17, 18, 20 and 21, Proposition 9.20 and the inclusions of
the dual space), `Numlib.Analysis.Sobolev.Operators` (Lemma 9.5), `Numlib.Analysis.Sobolev.Poincare`
(Corollary 9.19 and Remark 21), `Numlib.Analysis.Sobolev.EmbeddingDomain` and
`Numlib.Analysis.Sobolev.Compactness` (Remark 20), and `Numlib.Analysis.PDE.Elliptic.Dirichlet` (the
scalar product of $H_0^1(\Omega)$).

## Main definitions

* Section 9.4, Definition, `Brezis.Chapter09.sobolevZeroSpace`: the space $W_0^{1,p}(\Omega)$, a
  closed subspace of $W^{1,p}(\Omega)$.
* Section 9.4, Definition, `Brezis.Chapter09.hZeroSpace`: the space
  $H_0^1(\Omega) = W_0^{1,2}(\Omega)$.
* Remark 20, `Brezis.Chapter09.IsContinuousInjectionLpZero` and
  `Brezis.Chapter09.IsCompactInjectionLpZero`: $W_0^{1,p}(\Omega) \subset L^q(\Omega)$ with
  continuous, or compact, injection.
* Remark 20, `Brezis.Chapter09.toContinuousMapClosureZero`: for bounded $\Omega$ and $p > N$, the
  injection $W_0^{1,p}(\Omega) \subset C(\bar\Omega)$.
* Remark 22, `Brezis.Chapter09.sobolevZeroSpaceHigher`: the space $W_0^{m,p}(\Omega)$.
* Section 9.4, the dual space, `Brezis.Chapter09.dualSpace` and `Brezis.Chapter09.hMinusOne`: the
  spaces $W^{-1,p'}(\Omega)$ and $H^{-1}(\Omega)$.

## Main results

* Section 9.4, Definition, `Brezis.Chapter09.sobolevZeroSpace_banach`: $W_0^{1,p}(\Omega)$ is a
  separable Banach space, reflexive for $p > 1$, and $H_0^1(\Omega)$ is a Hilbert space.
* Remark 17, `Brezis.Chapter09.remark_9_17`: $W_0^{1,p}(\mathbb{R}^N) = W^{1,p}(\mathbb{R}^N)$; for
  the punctured space see `Brezis.Chapter09.remark_9_17_punctured` and
  `Brezis.Chapter09.remark_9_17_punctured_of_le`.
* Remark 18, `Brezis.Chapter09.remark_9_18` and `Brezis.Chapter09.remark_9_18_closure`:
  $C_c^1(\Omega) \subset W_0^{1,p}(\Omega)$, and $C_c^\infty(\Omega)$ gives the same closure.
* Lemma 9.5, `Brezis.Chapter09.lemma_9_5`: if $u \in W^{1,p}(\Omega)$ vanishes outside a compact
  subset of $\Omega$, then $u \in W_0^{1,p}(\Omega)$.
* Theorem 9.17, `Brezis.Chapter09.theorem_9_17`: for $\Omega$ of class $C^1$ and
  $u \in W^{1,p}(\Omega) \cap C(\bar\Omega)$, $u = 0$ on $\Gamma$ if and only if
  $u \in W_0^{1,p}(\Omega)$; the directions are `Brezis.Chapter09.theorem_9_17_mp` and
  `Brezis.Chapter09.theorem_9_17_mpr`.
* Remark 19, `Brezis.Chapter09.remark_9_19`: the implication (i) $\Rightarrow$ (ii) of Theorem 9.17
  holds on every open set.
* Proposition 9.18, `Brezis.Chapter09.proposition_9_18`: three equivalent characterizations of
  $W_0^{1,p}(\Omega)$; the implications are `Brezis.Chapter09.proposition_9_18_i_ii`,
  `Brezis.Chapter09.proposition_9_18_ii_iii`, `Brezis.Chapter09.proposition_9_18_i_iii` and
  `Brezis.Chapter09.proposition_9_18_iii_i`.
* Remark 20, `Brezis.Chapter09.remark_9_20`: Corollary 9.14 on $W_0^{1,p}(\Omega)$ for every open
  set, Theorem 9.16 on $W_0^{1,p}(\Omega)$ for every bounded open set, and
  $\|u\|_{p^*} \le C \|\nabla u\|_p$ on $W_0^{1,p}(\Omega)$; the parts are
  `Brezis.Chapter09.remark_9_20_embedding`, `Brezis.Chapter09.remark_9_20_compact` and
  `Brezis.Chapter09.remark_9_20_sobolev`.
* Corollary 9.19 (Poincaré's inequality), `Brezis.Chapter09.corollary_9_19`: for bounded $\Omega$,
  $\|u\|_p \le C \|\nabla u\|_p$ on $W_0^{1,p}(\Omega)$; the consequences are
  `Brezis.Chapter09.corollary_9_19_gradNorm`, `Brezis.Chapter09.corollary_9_19_norm` and
  `Brezis.Chapter09.corollary_9_19_inner`.
* Remark 21, `Brezis.Chapter09.remark_9_21`: Poincaré's inequality for $\Omega$ of finite measure
  and for $\Omega$ in a slab; the parts are `Brezis.Chapter09.remark_9_21_measure` and
  `Brezis.Chapter09.remark_9_21_projection`.
* Remark 22, `Brezis.Chapter09.sobolevZeroSpaceHigher_eq_closure_contDiff`: $W_0^{m,p}(\Omega)$ is
  the closure of $C_c^m(\Omega)$ in $W^{m,p}(\Omega)$.
* Section 9.4, the dual space, `Brezis.Chapter09.dual_inclusions` and
  `Brezis.Chapter09.dual_inclusions_of_le`: the continuous dense injections $H_0^1(\Omega) \subset
  L^2(\Omega) \subset H^{-1}(\Omega)$ and $W_0^{1,p}(\Omega) \subset L^2(\Omega) \subset
  W^{-1,p'}(\Omega)$.
* Proposition 9.20, `Brezis.Chapter09.proposition_9_20`: every $F \in W^{-1,p'}(\Omega)$ is $v
  \mapsto \int f_0 v + \sum_i \int f_i \, \partial v / \partial x_i$ with $f_i \in L^{p'}(\Omega)$;
  for bounded $\Omega$ one can take $f_0 = 0$ (`Brezis.Chapter09.proposition_9_20_bounded`).

## Conventions

* The space $W_0^{1,p}(\Omega)$ is the submodule `Brezis.Chapter09.sobolevZeroSpace N p Ω` of
  `Brezis.Chapter09.sobolevSpace N p Ω`, so $u \in W_0^{1,p}(\Omega)$ is membership in a submodule.
  A function $u : \mathbb{R}^N \to \mathbb{R}$ "belongs to $W_0^{1,p}(\Omega)$" when it is a.e. on
  $\Omega$ the function of an element of this submodule.
* A function $u \in W^{1,p}(\Omega) \cap C(\bar\Omega)$ is an element $u$ of $W^{1,p}(\Omega)$
  together with a function $\tilde u$ that is continuous on $\bar\Omega$ and equals $u$ a.e. on
  $\Omega$.
* The results that need $\Omega$ of class $C^1$ (Theorem 9.17, (ii) $\Rightarrow$ (i), and
  Proposition 9.18, (iii) $\Rightarrow$ (i)) use `Brezis.Chapter09.IsClassC1` of Section 9.2 on
  $\mathbb{R}^{d+1}$, so $N = d + 1$ there. Corollary 9.19, the bounded-projection clause of Remark
  21 and the combined Remark 21, the last sentence of Proposition 9.20 and the inclusions
  $W_0^{1,p}(\Omega) \subset L^2(\Omega) \subset W^{-1,p'}(\Omega)$ are also stated on
  $\mathbb{R}^{d+1}$, that is, for $N \ge 1$. The other results are stated for every $N$.
* $\|\nabla u\|_{L^p(\Omega)}$ is `eLpNorm (Brezis.Chapter09.gradient u) p`, as in Sections 9.1 and
  9.3. The norm of the Lean type of $W^{1,p}(\Omega)$ is written $\|u\|$, and the norm of the source
  is $\|u\|_{W^{1,p}}$ (`Brezis.Chapter09.bookNorm`).

## Implementation notes

* The submodule `Brezis.Chapter09.sobolevZeroSpace N p Ω` is the backbone's
  `SobolevEuclideanZero N 1 p Ω`, the closure of the test functions $\mathcal{D}(\Omega)$ in
  $W^{1,p}(\Omega)$. By Remark 18 (`Brezis.Chapter09.remark_9_18_closure`) this is the closure of
  $C_c^1(\Omega)$ for $p < \infty$. The definition also applies for $p = \infty$, where the source
  does not define the space.
* The backbone measures the gradient by the $\ell^p$ norm `SobolevMultiIndex.gradNorm u`
  $= (\sum_i \|\partial_i u\|_p^p)^{1/p}$. It is compared with $\|\nabla u\|_p$ by
  `Brezis.Chapter09.gradNorm_le_eLpNorm_gradient` and
  `Brezis.Chapter09.toReal_eLpNorm_gradient_le_gradNorm`, and at $p = 2$ the two agree
  (`Brezis.Chapter09.gradNorm_eq_toReal_eLpNorm_gradient_two`).

## Deviations from the source

* **Remark 17, punctured space** (reading). The condition "$\mathbb{R}^N \setminus \Omega$
  sufficiently thin and $p < N$" is informal. The statement here takes
  $\Omega = \mathbb{R}^N \setminus \{0\}$ with $N \ge 2$, and includes $p = N$. See
  `Brezis.Chapter09.remark_9_17_punctured_of_le`.
* **Proposition 9.18** (generalization). The implications (i) $\Rightarrow$ (ii) and (i)
  $\Rightarrow$ (iii) are proved for $1 \le p \le \infty$, and (ii) $\Rightarrow$ (iii) for
  $1 < p \le \infty$, all on an arbitrary open set. See `Brezis.Chapter09.proposition_9_18_i_ii`,
  `Brezis.Chapter09.proposition_9_18_ii_iii` and `Brezis.Chapter09.proposition_9_18_i_iii`.
* **Remark 20** (reading). The clauses for $p = N$ assume $N \ge 2$, as Corollary 9.14. The
  constants of the Hölder estimate and of the Sobolev inequality are stated for each fixed $\Omega$;
  the independence of $\Omega$ that the source states is not recorded. See
  `Brezis.Chapter09.remark_9_20`.
* **Remark 21** (reading). The finite-measure clause is stated for $N \ge 2$, and the
  bounded-projection clause for the last coordinate axis. See `Brezis.Chapter09.remark_9_21`.
* **Proposition 9.20** (reading). The source states $\|F\| = \max_i \|f_i\|_{p'}$, which refers to
  the norm $\sum_i \|h_i\|_p$ on $(L^p)^{N+1}$. The statement here gives the bound
  $\|f_i\|_{p'} \le \|F\|$ for the norm of the Lean type. See `Brezis.Chapter09.proposition_9_20`.
* **The inclusions $W_0^{1,p}(\Omega) \subset L^2(\Omega) \subset W^{-1,p'}(\Omega)$** (correction).
  The range $2N/(N + 2) \le p$ of the source contains $p = 1$ for $N \le 2$, where $L^2(\Omega)$ is
  not dense in $W^{-1,\infty}(\Omega)$. The statement assumes $p > 1$. See
  `Brezis.Chapter09.dual_inclusions_of_le`.

## Not formalized

* **Remark 21, the case $N = 1$ of the finite-measure clause.**
* **Remark 22, the heuristic and the comparison.** The heuristic "$D^\alpha u = 0$ on $\Gamma$ for
  $|\alpha| \le m - 1$", and the difference between $W_0^{m,p}(\Omega)$ and
  $W^{m,p}(\Omega) \cap W_0^{1,p}(\Omega)$ for $m \ge 2$.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

/-! ### The Definition -/

section Definition

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of $\mathbb{R}^N$, as a basis of the module. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **Section 9.4** of [brezis2011functional], Definition. Let $1 \le p \le \infty$ and let
$\Omega \subseteq \mathbb{R}^N$ be open. The space **$W_0^{1,p}(\Omega)$** is the closure of the
test functions $\mathcal{D}(\Omega)$ in $W^{1,p}(\Omega)$, as a submodule of $W^{1,p}(\Omega)$.

The source defines $W_0^{1,p}(\Omega)$, for $1 \le p < \infty$, as the closure of
$C_c^1(\Omega)$ in $W^{1,p}(\Omega)$. The two closures agree by Remark 18
(`Brezis.Chapter09.remark_9_18_closure`). The definition is the backbone's
`SobolevEuclideanZero N 1 p Ω`. -/
noncomputable abbrev sobolevZeroSpace (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Submodule ℝ (sobolevSpace N p Ω) :=
  SobolevEuclideanZero N 1 p Ω

/-- **Section 9.4** of [brezis2011functional], Definition. The space **$H_0^1(\Omega)$** is
$W_0^{1,2}(\Omega)$, a submodule of $H^1(\Omega)$ (footnote 19). -/
noncomputable abbrev hZeroSpace (N : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin N))) :
    Submodule ℝ (hSpace N Ω) :=
  sobolevZeroSpace N 2 Ω

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Section 9.4** of [brezis2011functional], Definition, second sentence. Let $1 \le p < \infty$.
The space $W_0^{1,p}(\Omega)$ with the norm of $W^{1,p}(\Omega)$ is a separable Banach space,
and it is reflexive if $1 < p < \infty$. The space $H_0^1(\Omega)$ with the scalar product of
$H^1(\Omega)$ is a Hilbert space, where
$$(u, v)_{H^1} = \int_\Omega u v + \sum_{i=1}^N \int_\Omega \frac{\partial u}{\partial x_i}
  \frac{\partial v}{\partial x_i}.$$

All of this holds because $W_0^{1,p}(\Omega)$ is a closed subspace of $W^{1,p}(\Omega)$
(Proposition 9.1). The scalar product formula is `Brezis.Chapter09.hInner`, and separability and
reflexivity are `Brezis.Chapter03.IsSeparable` and `Brezis.Chapter03.IsReflexive`. -/
theorem sobolevZeroSpace_banach (hp' : p ≠ ⊤) :
    CompleteSpace (sobolevZeroSpace N p Ω) ∧ Chapter03.IsSeparable (sobolevZeroSpace N p Ω) ∧
    (1 < p → Chapter03.IsReflexive (sobolevZeroSpace N p Ω)) ∧
    (CompleteSpace (hZeroSpace N Ω) ∧ ∀ u v : hZeroSpace N Ω,
      inner ℝ u v = (∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (u : hSpace N Ω) x
        * SobolevMultiIndex.fn (v : hSpace N Ω) x)
        + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u : hSpace N Ω) i x
          * partialDeriv (v : hSpace N Ω) i x) := by
  refine ⟨inferInstance, ?_, fun hp ↦ ?_, inferInstance, fun u v ↦ ?_⟩
  · have := Fact.mk hp'
    exact (Chapter03.separable_iff _).2 inferInstance
  · have := Chapter04.theorem_4_10 (μ := volume.restrict (Ω : Set 𝔼)) hp hp'
    exact Chapter03.isReflexive_iff.2 inferInstance
  · rw [Submodule.coe_inner, hInner]

/-- **Remark 17** of Chapter 9 of [brezis2011functional]. Let $1 \le p < \infty$. Then
$W_0^{1,p}(\mathbb{R}^N) = W^{1,p}(\mathbb{R}^N)$.

The reason is that $C_c^1(\mathbb{R}^N)$ is dense in $W^{1,p}(\mathbb{R}^N)$ (Theorem 9.2). The
proof specializes `SobolevEuclideanZero.eq_top`. The sentence of the remark "by contrast, in
general $W_0^{1,p}(\Omega) \ne W^{1,p}(\Omega)$" is the content of Theorem 9.17. The punctured
space is `Brezis.Chapter09.remark_9_17_punctured`. -/
theorem remark_9_17 (hp' : p ≠ ⊤) : sobolevZeroSpace N p ⊤ = ⊤ :=
  SobolevEuclideanZero.eq_top hp'

/-- **Remark 17** of Chapter 9 of [brezis2011functional], the punctured space. Let $N \ge 2$ and
$\Omega = \mathbb{R}^N \setminus \{0\}$. Then $H_0^1(\Omega) = H^1(\Omega)$.

The proof specializes `SobolevEuclideanZero.eq_top_of_compl_singleton`: a point has zero
capacity in $H^1$ for $N \ge 2$. This is also the example of Remark 19. The converse of Theorem
9.17 fails without smoothness of $\Omega$, because a function of
$H^1(\Omega) \cap C(\bar\Omega)$ with $u(0) \ne 0$ lies in $H_0^1(\Omega)$. -/
theorem remark_9_17_punctured (hN : 2 ≤ N) :
    hZeroSpace N ⟨{0}ᶜ, isOpen_compl_singleton⟩ = ⊤ :=
  SobolevEuclideanZero.eq_top_of_compl_singleton hN (by exact_mod_cast hN) rfl

/-- **Remark 17** of Chapter 9 of [brezis2011functional], the punctured space in $W^{1,p}$. Let
$N \ge 2$, $1 \le p \le N$ and $\Omega = \mathbb{R}^N \setminus \{0\}$. Then
$W_0^{1,p}(\Omega) = W^{1,p}(\Omega)$.

**Reading.** The source states that $W_0^{1,p}(\Omega) = W^{1,p}(\Omega)$ "if
$\mathbb{R}^N \setminus \Omega$ is sufficiently thin and $p < N$", without a precise condition.
The statement here takes the complement of one point, and also includes the endpoint $p = N$. -/
theorem remark_9_17_punctured_of_le (hN : 2 ≤ N) (hp : p ≤ N) :
    sobolevZeroSpace N p ⟨{0}ᶜ, isOpen_compl_singleton⟩ = ⊤ :=
  SobolevEuclideanZero.eq_top_of_compl_singleton hN hp rfl

/-- **Remark 18** of Chapter 9 of [brezis2011functional]. Let $1 \le p < \infty$ and let
$v : \mathbb{R}^N \to \mathbb{R}$ be of class $C^1$ with compact support contained in $\Omega$.
Then $v$ belongs to $W_0^{1,p}(\Omega)$: there is $u \in W_0^{1,p}(\Omega)$ with $u = v$ a.e. on
$\Omega$.

This is the inclusion $C_c^1(\Omega) \subset W_0^{1,p}(\Omega)$ of the definition of the source.
The proof specializes `SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport`, which follows
from Lemma 9.5. -/
theorem remark_9_18 (hp' : p ≠ ⊤) {v : 𝔼 → ℝ} (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (hvΩ : tsupport v ⊆ Ω) :
    ∃ u ∈ sobolevZeroSpace N p Ω, SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v :=
  SobolevEuclidean.mem_zero_of_contDiff_hasCompactSupport hp' hv hvc hvΩ

/-- **Remark 18** of Chapter 9 of [brezis2011functional], "in other words". Let $1 \le p < \infty$.
The closure in $W^{1,p}(\Omega)$ of the functions that are a.e. on $\Omega$ equal to a $C^1$
function with compact support in $\Omega$ is $W_0^{1,p}(\Omega)$. Thus $C_c^\infty(\Omega)$ and
$C_c^1(\Omega)$ give the same space $W_0^{1,p}(\Omega)$.

The inclusion $\subseteq$ holds because `Brezis.Chapter09.remark_9_18` puts $C_c^1(\Omega)$ in
the closed subspace $W_0^{1,p}(\Omega)$. The inclusion $\supseteq$ holds because a test function
is a $C^1$ function with compact support in $\Omega$. -/
theorem remark_9_18_closure (hp' : p ≠ ⊤) :
    closure {u : sobolevSpace N p Ω | ∃ v : 𝔼 → ℝ, ContDiff ℝ 1 v ∧ HasCompactSupport v ∧
        tsupport v ⊆ Ω ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v}
      = (sobolevZeroSpace N p Ω : Set (sobolevSpace N p Ω)) := by
  apply subset_antisymm
  · refine closure_minimal ?_ SobolevMultiIndexZero.isClosed
    rintro u ⟨v, hv, hvc, hvΩ, hu⟩
    exact SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset hp' u hvc hvΩ hu
  · rw [show (sobolevZeroSpace N p Ω : Set (sobolevSpace N p Ω))
        = closure (SobolevMultiIndex.testFunctions ℝ 𝔟 1 p Ω volume : Set (sobolevSpace N p Ω))
        from Submodule.topologicalClosure_coe _]
    refine closure_mono ?_
    rintro u ⟨φ, hφ⟩
    exact ⟨φ, φ.contDiff.of_le (by simp), φ.hasCompactSupport, φ.tsupport_subset, hφ⟩

/-- **Lemma 9.5** of [brezis2011functional]. Let $1 \le p < \infty$ and $u \in W^{1,p}(\Omega)$.
Assume that there is a compact set $K \subseteq \Omega$ such that $u = 0$ a.e. on
$\Omega \setminus K$, that is, $\operatorname{supp} u$ is a compact subset of $\Omega$. Then
$u \in W_0^{1,p}(\Omega)$.

The proof specializes `SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact`. The proof of
the source takes an open set $\omega$ with $\operatorname{supp} u \subset \omega \subset\subset
\Omega$, a cut-off function $\alpha \in C_c^1(\omega)$ with $\alpha = 1$ on
$\operatorname{supp} u$, and uses Theorem 9.2. -/
theorem lemma_9_5 (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) {K : Set 𝔼} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hu : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), x ∉ K → SobolevMultiIndex.fn u x = 0) :
    u ∈ sobolevZeroSpace N p Ω :=
  SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact hp' u hK hKΩ hu

/-! ### Theorem 9.17 -/

/-- **Theorem 9.17** of [brezis2011functional], (i) $\Rightarrow$ (ii), on an arbitrary open set.
Let $1 \le p < \infty$, $u \in W^{1,p}(\Omega)$, and let
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\bar\Omega$ with $u = \tilde u$ a.e.
on $\Omega$. If $\tilde u = 0$ on $\Gamma = \partial\Omega$, then $u \in W_0^{1,p}(\Omega)$.

Remark 19 states that this direction does not use the smoothness of $\Omega$. The proof
specializes `SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`. The truncations
$u_n = G(nu)/n$ of the proof of the source (with Proposition 9.5) have compact support in
$\Omega$, so they lie in $W_0^{1,p}(\Omega)$ by Lemma 9.5, and they converge to $u$ in
$W^{1,p}(\Omega)$. -/
theorem theorem_9_17_mp (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) {ũ : 𝔼 → ℝ}
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (h0 : EqOn ũ 0 (frontier (Ω : Set 𝔼))) :
    u ∈ sobolevZeroSpace N p Ω :=
  SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier hp' u hu hc h0

/-- **Remark 19** of Chapter 9 of [brezis2011functional], first sentence. Let
$\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, $1 \le p < \infty$,
$u \in W^{1,p}(\Omega)$, and let $\tilde u$ be continuous on $\bar\Omega$ with $u = \tilde u$
a.e. on $\Omega$. If $\tilde u = 0$ on $\partial\Omega$, then $u \in W_0^{1,p}(\Omega)$.

This is the implication (i) $\Rightarrow$ (ii) of Theorem 9.17 without a smoothness hypothesis,
`Brezis.Chapter09.theorem_9_17_mp`. The second sentence of the remark, that the converse fails
on $\Omega = \mathbb{R}^N \setminus \{0\}$, is the punctured space of Remark 17,
`Brezis.Chapter09.remark_9_17_punctured_of_le`. -/
theorem remark_9_19 (hp' : p ≠ ⊤) (u : sobolevSpace N p Ω) {ũ : 𝔼 → ℝ}
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (h0 : EqOn ũ 0 (frontier (Ω : Set 𝔼))) :
    u ∈ sobolevZeroSpace N p Ω :=
  theorem_9_17_mp hp' u hu hc h0

end Definition

section ClassC1

variable {d : ℕ}

/-- The space $\mathbb{R}^N$, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Theorem 9.17** of [brezis2011functional], (ii) $\Rightarrow$ (i). Let $\Omega$ be of class
$C^1$, $1 \le p < \infty$, $u \in W_0^{1,p}(\Omega)$, and let $\tilde u$ be continuous on
$\bar\Omega$ with $u = \tilde u$ a.e. on $\Omega$. Then $\tilde u = 0$ on
$\Gamma = \partial\Omega$.

The proof specializes `SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure`. Local charts
reduce the problem to $Q_+$, where $u \in W_0^{1,p}(Q_+) \cap C(\bar Q_+)$ vanishes on $Q_0$ by
the strip inequality $\varepsilon^{-1} \int_{|x'| < 1} \int_0^\varepsilon |u| \le \int_{|x'| <
1} \int_0^\varepsilon |\partial u / \partial x_N|$. -/
theorem theorem_9_17_mpr (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤)
    {u : sobolevSpace (d + 1) p Ω} (hu : u ∈ sobolevZeroSpace (d + 1) p Ω) {ũ : 𝔼 → ℝ}
    (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) : EqOn ũ 0 (frontier (Ω : Set 𝔼)) :=
  SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure hp' hΩ hu hũ hc

/-- **Theorem 9.17** of [brezis2011functional]. Let $\Omega$ be of class $C^1$, $1 \le p < \infty$,
and $u \in W^{1,p}(\Omega) \cap C(\bar\Omega)$, that is, $u \in W^{1,p}(\Omega)$ with a
representative $\tilde u$ that is continuous on $\bar\Omega$. Then the following properties are
equivalent: (i) $\tilde u = 0$ on $\Gamma$; (ii) $u \in W_0^{1,p}(\Omega)$.

By footnote 21 of the source, for $p > N$ the continuous representative exists for every $u$
(Corollary 9.14). -/
theorem theorem_9_17 (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤) (u : sobolevSpace (d + 1) p Ω)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) :
    EqOn ũ 0 (frontier (Ω : Set 𝔼)) ↔ u ∈ sobolevZeroSpace (d + 1) p Ω :=
  ⟨theorem_9_17_mp hp' u hũ hc, fun hu ↦ theorem_9_17_mpr hΩ hp' hu hũ hc⟩

end ClassC1

/-! ### Proposition 9.18 -/

section Prop18

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Proposition 9.18** of [brezis2011functional], (i) $\Rightarrow$ (ii), on an arbitrary open
set. Let $1 \le p \le \infty$ with conjugate exponent $p'$, and let
$u : \mathbb{R}^N \to \mathbb{R}$ belong to $W_0^{1,p}(\Omega)$. Then there is a constant $C$
such that
$$\Big|\int_\Omega u \frac{\partial \varphi}{\partial x_i}\Big| \le C
  \|\varphi\|_{L^{p'}(\Omega)} \quad \text{for all } \varphi \in C_c^1(\mathbb{R}^N) \text{ and
  all } i = 1, \dots, N.$$

**Generalization.** The source assumes $1 < p < \infty$. The implication holds for
$1 \le p \le \infty$ and every open set.

The proof specializes `SobolevEuclideanZero.abs_integral_fn_smul_fderiv_le` and takes for $C$
the $\ell^p$ gradient norm `SobolevMultiIndex.gradNorm`. For $u_n \in C_c^1(\Omega)$ with
$u_n \to u$ one has $|\int_\Omega u_n \partial_i \varphi| = |\int_\Omega \partial_i u_n \,
\varphi| \le \|\partial_i u_n\|_p \|\varphi\|_{p'}$, and one passes to the limit. -/
theorem proposition_9_18_i_ii [p.HolderConjugate q] {u : 𝔼 → ℝ}
    (h : ∃ v ∈ sobolevZeroSpace N p Ω,
      SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u) :
    ∃ C : ℝ, ∀ φ : 𝔼 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin N,
      |∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
        ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set 𝔼))).toReal := by
  obtain ⟨v, hv, hvu⟩ := h
  refine ⟨SobolevMultiIndex.gradNorm v, fun φ hφ hφc i ↦ ?_⟩
  have h1 := SobolevEuclideanZero.abs_integral_fn_smul_fderiv_le (q := q) ⟨v, hv⟩ hφ hφc i
  have e : ∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set 𝔼),
          SobolevMultiIndex.fn v x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    integral_congr_ae (hvu.symm.mono fun x hx ↦ by simp only [hx])
  rw [e]
  exact h1.trans (mul_le_mul_of_nonneg_right
    (SobolevMultiIndex.norm_weakDeriv_single_le_gradNorm v i) ENNReal.toReal_nonneg)

omit [Fact (1 ≤ p)] in
/-- **Proposition 9.18** of [brezis2011functional], (ii) $\Rightarrow$ (iii), on an arbitrary open
set. Let $1 < p \le \infty$ with conjugate exponent $p' < \infty$, and let $u \in L^p(\Omega)$.
Assume that there is a constant $C$ with
$$\Big|\int_\Omega u \frac{\partial \varphi}{\partial x_i}\Big| \le C
  \|\varphi\|_{L^{p'}(\Omega)} \quad \text{for all } \varphi \in C_c^1(\mathbb{R}^N) \text{ and
  all } i.$$
Then the extension by zero $\bar u$, equal to $u$ on $\Omega$ and to $0$ on
$\mathbb{R}^N \setminus \Omega$, belongs to $W^{1,p}(\mathbb{R}^N)$.

**Generalization.** The source assumes $1 < p < \infty$. The implication holds also for
$p = \infty$, and on every open set.

The proof specializes `SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le`. Since
$\int_{\mathbb{R}^N} \bar u \, \partial_i \varphi = \int_\Omega u \, \partial_i \varphi$ and
$\|\varphi\|_{L^{p'}(\Omega)} \le \|\varphi\|_{L^{p'}(\mathbb{R}^N)}$, this is Proposition 9.3
on $\mathbb{R}^N$. -/
theorem proposition_9_18_ii_iii [p.HolderConjugate q] (hq : q ≠ ⊤) {u : 𝔼 → ℝ}
    (hu : MemLp u p (volume.restrict (Ω : Set 𝔼)))
    (h : ∃ C : ℝ, ∀ φ : 𝔼 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin N,
      |∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
        ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set 𝔼))).toReal) :
    ∃ w : sobolevSpace N p ⊤, SobolevMultiIndex.fn w =ᵐ[volume] (Ω : Set 𝔼).indicator u := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨w, hw⟩ := (exists_fn_ae_eq_iff (N := N) (p := p) (Ω := ⊤) (m := 1) _).2
    (SobolevEuclidean.indicator_memSobolev_of_forall_abs_integral_le hq hu hC)
  exact ⟨w, by simpa [Measure.restrict_coe_top] using hw⟩

/-- **Proposition 9.18** of [brezis2011functional], (i) $\Rightarrow$ (iii), on an arbitrary open
set, with the derivatives. Let $1 \le p \le \infty$ and $u \in W_0^{1,p}(\Omega)$. Then the
extension by zero $\bar u$ of $u$ belongs to $W^{1,p}(\mathbb{R}^N)$, and $\partial \bar u /
\partial x_i = \overline{\partial u / \partial x_i}$ a.e. on $\mathbb{R}^N$ for every $i$, the
extension by zero of $\partial u / \partial x_i$.

**Generalization.** The source assumes $1 < p < \infty$. The implication holds for
$1 \le p \le \infty$ and every open set.

The proof uses the extension by zero of the backbone, `SobolevEuclideanZero.extendZeroL`, an
isometry $W_0^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$, with
`SobolevEuclideanZero.fn_extendZeroL` and `SobolevEuclideanZero.weakDeriv_extendZeroL_single`.
It does not use the Riesz representation theorem: the weak derivative is closed under $L^p$
limits, and one applies this to the extensions by zero of approximating test functions. -/
theorem proposition_9_18_i_iii {u : sobolevSpace N p Ω} (hu : u ∈ sobolevZeroSpace N p Ω) :
    ∃ w : sobolevSpace N p ⊤,
      SobolevMultiIndex.fn w =ᵐ[volume] (Ω : Set 𝔼).indicator (SobolevMultiIndex.fn u) ∧
      ∀ i, (partialDeriv w i : 𝔼 → ℝ) =ᵐ[volume] (Ω : Set 𝔼).indicator (partialDeriv u i) :=
  ⟨SobolevEuclideanZero.extendZeroL N p Ω ⟨u, hu⟩, SobolevEuclideanZero.fn_extendZeroL _,
    fun i ↦ SobolevEuclideanZero.weakDeriv_extendZeroL_single _ i⟩

end Prop18

section Prop18ClassC1

variable {d : ℕ}

/-- The space $\mathbb{R}^N$, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Proposition 9.18** of [brezis2011functional], (iii) $\Rightarrow$ (i). Let $\Omega$ be of
class $C^1$, $1 \le p < \infty$ and $u : \mathbb{R}^N \to \mathbb{R}$. If the extension by zero
$\bar u$ of $u$ belongs to $W^{1,p}(\mathbb{R}^N)$, then $u$ belongs to $W_0^{1,p}(\Omega)$.

The proof specializes `SobolevEuclideanZero.mem_of_indicator_memSobolev`. Local charts and a
partition of unity reduce the problem to $Q_+$. There one uses the one-sided mollifiers $\rho_n$
supported in $\{1/(2n) < x_N < 1/n\}$, for which $\rho_n \star (\alpha \bar u) \in C_c^1(Q_+)$. -/
theorem proposition_9_18_iii_i (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤) {u : 𝔼 → ℝ}
    (h : ∃ w : sobolevSpace (d + 1) p ⊤,
      SobolevMultiIndex.fn w =ᵐ[volume] (Ω : Set 𝔼).indicator u) :
    ∃ v ∈ sobolevZeroSpace (d + 1) p Ω,
      SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u := by
  obtain ⟨w, hw⟩ := h
  refine SobolevEuclideanZero.mem_of_indicator_memSobolev hp' hΩ ?_
  exact (exists_fn_ae_eq_iff (Ω := ⊤) (m := 1) _).1
    ⟨w, by simpa [Measure.restrict_coe_top] using hw⟩

/-- **Proposition 9.18** of [brezis2011functional]. Let $\Omega$ be of class $C^1$, $1 < p < \infty$
with conjugate exponent $p'$, and $u \in L^p(\Omega)$. The following properties are equivalent:
(i) $u \in W_0^{1,p}(\Omega)$; (ii) there is a constant $C$ such that $|\int_\Omega u \,
\partial \varphi / \partial x_i| \le C \|\varphi\|_{L^{p'}(\Omega)}$ for all
$\varphi \in C_c^1(\mathbb{R}^N)$ and all $i = 1, \dots, N$; (iii) the function $\bar u$, equal
to $u$ on $\Omega$ and to $0$ on $\mathbb{R}^N \setminus \Omega$, belongs to
$W^{1,p}(\mathbb{R}^N)$.

In this case $\partial \bar u / \partial x_i = \overline{\partial u / \partial x_i}$
(`Brezis.Chapter09.proposition_9_18_i_iii`). Only (iii) $\Rightarrow$ (i) uses the regularity of
$\Omega$. -/
theorem proposition_9_18 (hΩ : IsClassC1 (Ω : Set 𝔼)) [p.HolderConjugate q] (hp : 1 < p)
    (hp' : p ≠ ⊤) {u : 𝔼 → ℝ} (hu : MemLp u p (volume.restrict (Ω : Set 𝔼))) :
    [∃ v ∈ sobolevZeroSpace (d + 1) p Ω,
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] u,
      ∃ C : ℝ, ∀ φ : 𝔼 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin (d + 1),
        |∫ x in (Ω : Set 𝔼), u x * fderiv ℝ φ x (EuclideanSpace.single i 1)|
          ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set 𝔼))).toReal,
      ∃ w : sobolevSpace (d + 1) p ⊤,
        SobolevMultiIndex.fn w =ᵐ[volume] (Ω : Set 𝔼).indicator u].TFAE := by
  have hq : q ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (p := q) (q := p)).2 hp).ne
  tfae_have 1 → 2 := proposition_9_18_i_ii
  tfae_have 2 → 3 := proposition_9_18_ii_iii hq hu
  tfae_have 3 → 1 := proposition_9_18_iii_i hΩ hp'
  tfae_finish

end Prop18ClassC1

/-! ### Remark 20: the embeddings of $W_0^{1,p}(\Omega)$ for an arbitrary open set -/

/-- **Remark 20** of Chapter 9 of [brezis2011functional], "with continuous injection" for
$W_0^{1,p}(\Omega)$. Let $1 \le p, q \le \infty$ and $\Omega \subseteq \mathbb{R}^N$ open. Then
**$W_0^{1,p}(\Omega) \subset L^q(\Omega)$ with continuous injection** if every function of
$W_0^{1,p}(\Omega)$ lies in $L^q(\Omega)$ and the inclusion $W_0^{1,p}(\Omega) \to L^q(\Omega)$
is a continuous embedding.

This is `Brezis.Chapter09.IsContinuousInjectionLp` of Section 9.3 for the subspace
$W_0^{1,p}(\Omega)$. The inclusion is `SobolevMultiIndex.toLpₗOn`. -/
def IsContinuousInjectionLpZero (N : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ h : ∀ u : sobolevZeroSpace N p Ω, MemLp (SobolevMultiIndex.fn (u : sobolevSpace N p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    IsContinuousEmbedding (SobolevMultiIndex.toLpₗOn ℝ
      (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) 1 p Ω volume
      (sobolevZeroSpace N p Ω) h)

/-- **Remark 20** of Chapter 9 of [brezis2011functional], "with compact injection" for
$W_0^{1,p}(\Omega)$. Let $1 \le p, q \le \infty$ and $\Omega \subseteq \mathbb{R}^N$ open. Then
**$W_0^{1,p}(\Omega) \subset L^q(\Omega)$ with compact injection** if every function of
$W_0^{1,p}(\Omega)$ lies in $L^q(\Omega)$ and the inclusion $W_0^{1,p}(\Omega) \to L^q(\Omega)$
is a compact embedding. -/
def IsCompactInjectionLpZero (N : ℕ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ h : ∀ u : sobolevZeroSpace N p Ω, MemLp (SobolevMultiIndex.fn (u : sobolevSpace N p Ω)) q
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    IsCompactEmbedding (SobolevMultiIndex.toLpₗOn ℝ
      (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)) 1 p Ω volume
      (sobolevZeroSpace N p Ω) h)

section Remark20

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- If $W_0^{1,p}(\Omega) \subset L^q(\Omega)$ with compact injection, then
$W_0^{1,p}(\Omega) \subset L^q(\Omega)$ with continuous injection. -/
theorem IsCompactInjectionLpZero.isContinuousInjectionLpZero [Fact (1 ≤ (q : ℝ≥0∞))]
    (h : IsCompactInjectionLpZero N p q Ω) : IsContinuousInjectionLpZero N p q Ω :=
  let ⟨h, hc⟩ := h
  ⟨h, hc.toIsContinuousEmbedding⟩

/-- **Remark 20** of Chapter 9 of [brezis2011functional], Corollary 9.14 on $W_0^{1,p}(\Omega)$, the
case $p < N$. Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, $1 \le p < N$ and
$1/p^* = 1/p - 1/N$. Then $W_0^{1,p}(\Omega) \subset L^q(\Omega)$ with continuous injection for
every $q \in [p, p^*]$.

The extension by zero (`SobolevEuclideanZero.hasSobolevExtensionOn`) replaces the extension
operator of Theorem 9.7. The proof specializes
`SobolevEuclideanZero.isContinuousEmbedding_toLp_of_lt`. -/
theorem remark_9_20_embedding_lt [Fact (1 ≤ (q : ℝ≥0∞))] {p' : ℝ≥0} (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hpq : p ≤ q) (hqp' : q ≤ p') :
    IsContinuousInjectionLpZero N p q Ω :=
  ⟨_, SobolevEuclideanZero.isContinuousEmbedding_toLp_of_lt hpN hp' hpq hqp'⟩

/-- **Remark 20** of Chapter 9 of [brezis2011functional], Corollary 9.14 on $W_0^{1,p}(\Omega)$, the
case $p = N$. Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set and $N \ge 2$. Then
$W_0^{1,N}(\Omega) \subset L^q(\Omega)$ with continuous injection for every
$q \in [N, +\infty)$.

**Reading.** The case is stated for $N \ge 2$, as Corollary 9.14 for $p = N$.

The proof specializes `SobolevEuclideanZero.isContinuousEmbedding_toLp_of_eq`. -/
theorem remark_9_20_embedding_eq [Fact (1 ≤ (q : ℝ≥0∞))] (hN : 2 ≤ N) (hp : p = (N : ℝ≥0))
    (hq : p ≤ q) : IsContinuousInjectionLpZero N p q Ω := by
  subst hp
  have : Fact (1 ≤ (N : ℝ≥0∞)) := ‹_›
  exact ⟨_, SobolevEuclideanZero.isContinuousEmbedding_toLp_of_eq hN hq⟩

/-- **Remark 20** of Chapter 9 of [brezis2011functional], Corollary 9.14 on $W_0^{1,p}(\Omega)$, the
case $p > N$, the injection. Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set and
$N < p < \infty$. Then $W_0^{1,p}(\Omega) \subset L^\infty(\Omega)$ with continuous injection.

The proof specializes `SobolevEuclideanZero.isContinuousEmbedding_toLp_top_of_lt`. -/
theorem remark_9_20_embedding_gt (hp : (N : ℝ≥0) < p) : IsContinuousInjectionLpZero N p ⊤ Ω :=
  ⟨_, SobolevEuclideanZero.isContinuousEmbedding_toLp_top_of_lt hp⟩

/-- **Remark 20** of Chapter 9 of [brezis2011functional], Corollary 9.14 on $W_0^{1,p}(\Omega)$, the
case $p > N$, the Hölder estimate. Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set,
$N < p < \infty$ and $\alpha = 1 - N/p$. There is a constant $C \ge 0$ such that every
$u \in W_0^{1,p}(\Omega)$ has a representative $\tilde u$ that is continuous on $\bar\Omega$ and
satisfies
$$|\tilde u(x) - \tilde u(y)| \le C \|u\|_{W^{1,p}} |x - y|^\alpha \quad \text{for all } x, y
  \in \bar\Omega,$$
and hence $|u(x) - u(y)| \le C \|u\|_{W^{1,p}} |x - y|^\alpha$ for a.e. $x$ and a.e. $y$ in
$\Omega$. In particular $W_0^{1,p}(\Omega) \subset C(\bar\Omega)$.

**Reading.** The source has a constant $C(p, N)$. Here $\Omega$ is fixed before the constant, so
the statement does not record that $C$ is independent of $\Omega$.

The proof specializes `SobolevEuclideanZero.exists_forall_continuous_holderWith_ae_eq`. Its
representative is Morrey's representative of the extension by zero, which is continuous on all
of $\mathbb{R}^N$. -/
theorem remark_9_20_embedding_holder (hp : (N : ℝ≥0) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevZeroSpace N p Ω, ∃ ũ : 𝔼 → ℝ,
      ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn (u : sobolevSpace N p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
        |ũ x - ũ y| ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p)) ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
        |SobolevMultiIndex.fn (u : sobolevSpace N p Ω) x
            - SobolevMultiIndex.fn (u : sobolevSpace N p Ω) y|
          ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p) := by
  obtain ⟨C, hC⟩ := SobolevEuclideanZero.exists_forall_continuous_holderWith_ae_eq
    (N := N) (p := p) (Ω := Ω) hp
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hα : ((1 - (N : ℝ≥0) / p : ℝ≥0) : ℝ) = 1 - (N : ℝ) / p := by
    rw [NNReal.coe_sub ((div_le_one (by exact_mod_cast hp0)).2 hp.le)]
    simp
  refine ⟨C, C.coe_nonneg, fun u ↦ ?_⟩
  obtain ⟨ũ, hc, hae, hh, -⟩ := hC u
  have hbound : ∀ x y, |ũ x - ũ y|
      ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p) := by
    intro x y
    have h1 := hh.dist_le x y
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, hα] at h1
    refine h1.trans ?_
    gcongr
    exact (bookNorm_equiv (u : sobolevSpace N p Ω)).1
  refine ⟨ũ, hc.continuousOn, hae, fun x _ y _ ↦ hbound x y, ?_⟩
  filter_upwards [hae] with x hx
  filter_upwards [hae] with y hy
  rw [hx, hy]
  exact hbound x y

/-- **Remark 20** of Chapter 9 of [brezis2011functional], first clause. Let
$\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set and $1 \le p < \infty$. Then the
conclusion of Corollary 9.14 holds for $W_0^{1,p}(\Omega)$, with continuous injections:
$$W_0^{1,p}(\Omega) \subset L^q(\Omega) \text{ for all } q \in [p, p^*], \ \frac{1}{p^*} =
  \frac{1}{p} - \frac{1}{N}, \quad \text{if } p < N,$$
$$W_0^{1,p}(\Omega) \subset L^q(\Omega) \text{ for all } q \in [N, +\infty), \quad \text{if }
  p = N \text{ and } N \ge 2,$$
$$W_0^{1,p}(\Omega) \subset L^\infty(\Omega), \quad \text{if } p > N.$$
If $p > N$, then moreover $W_0^{1,p}(\Omega) \subset C(\bar\Omega)$ with the Hölder estimate of
`Brezis.Chapter09.remark_9_20_embedding_holder`.

**Reading.** The case $p = N$ assumes $N \ge 2$, and the constant of the Hölder estimate may
depend on $\Omega$; see `Brezis.Chapter09.remark_9_20_embedding_eq` and
`Brezis.Chapter09.remark_9_20_embedding_holder`.

No regularity of $\Omega$ is needed, because the extension by zero is valid on every open set
(Proposition 9.18, (i) $\Rightarrow$ (iii)). -/
theorem remark_9_20_embedding :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ → p ≤ q →
      q ≤ p' → IsContinuousInjectionLpZero N p q Ω) ∧
    (2 ≤ N → p = (N : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsContinuousInjectionLpZero N p q Ω) ∧
    ((N : ℝ≥0) < p → IsContinuousInjectionLpZero N p ⊤ Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevZeroSpace N p Ω, ∃ ũ : 𝔼 → ℝ,
        ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
        SobolevMultiIndex.fn (u : sobolevSpace N p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
        (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
          |ũ x - ũ y| ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p)) ∧
        ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
          |SobolevMultiIndex.fn (u : sobolevSpace N p Ω) x
              - SobolevMultiIndex.fn (u : sobolevSpace N p Ω) y|
            ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p)) :=
  ⟨fun _ _ _ hpN hp' hpq hqp' ↦ remark_9_20_embedding_lt hpN hp' hpq hqp',
    fun hN hp _ _ hq ↦ remark_9_20_embedding_eq hN hp hq,
    fun hp ↦ ⟨remark_9_20_embedding_gt hp, remark_9_20_embedding_holder hp⟩⟩

/-! ### Remark 20: the compactness clause -/

/-- **Remark 20** of Chapter 9 of [brezis2011functional], Theorem 9.16 on $W_0^{1,p}(\Omega)$, the
case $p < N$. Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary bounded open set,
$1 \le p < N$ and $1/p^* = 1/p - 1/N$. Then $W_0^{1,p}(\Omega) \subset L^q(\Omega)$ with compact
injection for every $q \in [1, p^*)$.

The proof specializes `SobolevEuclideanZero.isCompactEmbedding_toLp_of_lt`, which needs only
$|\Omega| < \infty$. -/
theorem remark_9_20_compact_lt [Fact (1 ≤ (q : ℝ≥0∞))] (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {p' : ℝ≥0} (hpN : p < N) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) (hqp' : q < p') :
    IsCompactInjectionLpZero N p q Ω :=
  ⟨_, SobolevEuclideanZero.isCompactEmbedding_toLp_of_lt hb.measure_lt_top.ne hpN hp' hqp'⟩

/-- **Remark 20** of Chapter 9 of [brezis2011functional], Theorem 9.16 on $W_0^{1,p}(\Omega)$, the
case $p = N$. Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary bounded open set and
$N \ge 2$. Then $W_0^{1,N}(\Omega) \subset L^q(\Omega)$ with compact injection for every
$q \in [N, +\infty)$.

**Reading.** The case is stated for $N \ge 2$, as Theorem 9.16 for $p = N$.

The proof specializes `SobolevEuclideanZero.isCompactEmbedding_toLp_of_eq`. -/
theorem remark_9_20_compact_eq [Fact (1 ≤ (q : ℝ≥0∞))] (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hN : 2 ≤ N) (hp : p = (N : ℝ≥0)) (hq : p ≤ q) : IsCompactInjectionLpZero N p q Ω := by
  subst hp
  have : Fact (1 ≤ (N : ℝ≥0∞)) := ‹_›
  exact ⟨_, SobolevEuclideanZero.isCompactEmbedding_toLp_of_eq hb.measure_lt_top.ne hN hq⟩

/-- **Remark 20** of Chapter 9 of [brezis2011functional], the injection
$W_0^{1,p}(\Omega) \subset C(\bar\Omega)$. Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open
set and $N < p < \infty$. The **injection $W_0^{1,p}(\Omega) \subset C(\bar\Omega)$** is the
bounded linear map that sends $u$ to the restriction to the compact set $\bar\Omega$ of the
continuous representative of $u$ (`Brezis.Chapter09.remark_9_20_embedding_holder`).

The map is the backbone's `HasSobolevExtensionOn.toContinuousMapOnL` for the extension by zero. -/
noncomputable def toContinuousMapClosureZero (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hp : (N : ℝ≥0) < p) : sobolevZeroSpace N p Ω →L[ℝ] C(closure (Ω : Set 𝔼), ℝ) :=
  haveI : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  (SobolevEuclideanZero.hasSobolevExtensionOn (N := N) (p := p) (Ω := Ω)).toContinuousMapOnL hp
    (closure (Ω : Set 𝔼))

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set, $N < p < \infty$ and
$u \in W_0^{1,p}(\Omega)$. There is a continuous function $\tilde u$ on $\mathbb{R}^N$ with
$u = \tilde u$ a.e. on $\Omega$ whose restriction to $\bar\Omega$ is the image of $u$ under
`Brezis.Chapter09.toContinuousMapClosureZero`. -/
theorem exists_continuous_ae_eq_toContinuousMapClosureZero (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hp : (N : ℝ≥0) < p) (u : sobolevZeroSpace N p Ω) :
    ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧
      SobolevMultiIndex.fn (u : sobolevSpace N p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
      ∀ x : closure (Ω : Set 𝔼), toContinuousMapClosureZero hb hp u x = ũ x := by
  have : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  exact ⟨_, (SobolevEuclidean.contRep hp _).continuous,
    SobolevEuclideanZero.hasSobolevExtensionOn.fn_ae_eq_toContinuousMapOnL hp u, fun x ↦ rfl⟩

/-- **Remark 20** of Chapter 9 of [brezis2011functional], Theorem 9.16 on $W_0^{1,p}(\Omega)$, the
case $p > N$. Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary bounded open set and
$N < p < \infty$. Then the injection $W_0^{1,p}(\Omega) \subset C(\bar\Omega)$,
$u \mapsto \tilde u|_{\bar\Omega}$, is compact.

The injection is `Brezis.Chapter09.toContinuousMapClosureZero`. The proof specializes
`SobolevEuclideanZero.isCompactEmbedding_toContinuousMapOnL`, which uses the Ascoli–Arzelà
theorem. -/
theorem remark_9_20_compact_gt (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hp : (N : ℝ≥0) < p) :
    haveI : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
    IsCompactEmbedding (toContinuousMapClosureZero hb hp).toLinearMap := by
  have : CompactSpace (closure (Ω : Set 𝔼)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  exact SobolevEuclideanZero.isCompactEmbedding_toContinuousMapOnL hp subset_closure

/-- **Remark 20** of Chapter 9 of [brezis2011functional], Theorem 9.16 on $W_0^{1,p}(\Omega)$, "in
particular". Let $\Omega \subseteq \mathbb{R}^N$ be an arbitrary bounded open set and
$1 \le p < \infty$. Then $W_0^{1,p}(\Omega) \subset L^p(\Omega)$ with compact injection.

This holds for every $N$, including $N = p = 1$: at $q = p$ the Kolmogorov–Riesz argument needs
no case distinction. The proof specializes `SobolevEuclideanZero.isCompactEmbedding_toLp`. -/
theorem remark_9_20_compact_self (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    IsCompactInjectionLpZero N p p Ω :=
  ⟨_, SobolevEuclideanZero.isCompactEmbedding_toLp hb.measure_lt_top.ne⟩

/-- **Remark 20** of Chapter 9 of [brezis2011functional], second clause. Let
$\Omega \subseteq \mathbb{R}^N$ be an arbitrary bounded open set and $1 \le p < \infty$. Then
the conclusion of Theorem 9.16 holds for $W_0^{1,p}(\Omega)$: the following injections are
compact,
$$W_0^{1,p}(\Omega) \subset L^q(\Omega) \text{ for all } q \in [1, p^*), \quad \text{if } p <
  N,$$
$$W_0^{1,p}(\Omega) \subset L^q(\Omega) \text{ for all } q \in [p, +\infty), \quad \text{if }
  p = N \text{ and } N \ge 2,$$
$$W_0^{1,p}(\Omega) \subset C(\bar\Omega), \quad \text{if } p > N,$$
and $W_0^{1,p}(\Omega) \subset L^p(\Omega)$ with compact injection for all $p$ and all $N$.

**Reading.** The case $p = N$ assumes $N \ge 2$; see `Brezis.Chapter09.remark_9_20_compact_eq`. -/
theorem remark_9_20_compact (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ → q < p' →
      IsCompactInjectionLpZero N p q Ω) ∧
    (2 ≤ N → p = (N : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
      IsCompactInjectionLpZero N p q Ω) ∧
    (∀ hp : (N : ℝ≥0) < p,
      haveI : CompactSpace (closure (Ω : Set 𝔼)) :=
        isCompact_iff_compactSpace.1 hb.isCompact_closure
      IsCompactEmbedding (toContinuousMapClosureZero hb hp).toLinearMap) ∧
    IsCompactInjectionLpZero N p p Ω :=
  ⟨fun _ _ _ hpN hp' hqp' ↦ remark_9_20_compact_lt hb hpN hp' hqp',
    fun hN hp _ _ hq ↦ remark_9_20_compact_eq hb hN hp hq, remark_9_20_compact_gt hb,
    remark_9_20_compact_self hb⟩

/-! ### Remark 20: the Sobolev inequality on $W_0^{1,p}(\Omega)$ -/

/-- **Remark 20** of Chapter 9 of [brezis2011functional], last clause. Let
$\Omega \subseteq \mathbb{R}^N$ be an arbitrary open set, $1 \le p < N$ and $1/p^* = 1/p - 1/N$.
There is a constant $C$ with
$$\|u\|_{L^{p^*}(\Omega)} \le C \|\nabla u\|_{L^p(\Omega)} \quad \text{for all } u \in
  W_0^{1,p}(\Omega).$$

**Reading.** The source writes the constant $C(p, N)$. Here $\Omega$ is fixed before the
constant, so the statement does not record that $C$ is independent of $\Omega$. The proof gives
the constant of Theorem 9.9, $N$ times `SobolevEuclidean.gnsConst`, which does not depend on
$\Omega$.

The source says that the inequality "can also be deduced from Theorem 9.9": apply Theorem 9.9 to
the extension by zero $\bar u \in W^{1,p}(\mathbb{R}^N)$, whose gradient is the extension by
zero of $\nabla u$. The proof specializes `SobolevEuclideanZero.eLpNorm_fn_le_sum_of_eq`. -/
theorem remark_9_20_sobolev {p' : ℝ≥0} [Fact (1 ≤ (p' : ℝ≥0∞))] (hpN : p < N)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ u ∈ sobolevZeroSpace N p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p' (volume.restrict (Ω : Set 𝔼))
        ≤ C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  refine ⟨SobolevEuclidean.gnsConst N p * N, fun u hu ↦ ?_⟩
  refine (SobolevEuclideanZero.eLpNorm_fn_le_sum_of_eq hpN hp' ⟨u, hu⟩).trans ?_
  have h := sum_ofReal_norm_partialDeriv_le u
  push_cast
  rw [mul_assoc]
  exact mul_le_mul' le_rfl h

/-- **Remark 20** of Chapter 9 of [brezis2011functional]. The proof of Corollary 9.14 uses the
extension operator, so $\Omega$ must be smooth there. For $W_0^{1,p}(\Omega)$ one can use the
extension by zero, which is valid for every open set (Proposition 9.18, (i) $\Rightarrow$
(iii)). Let $\Omega \subseteq \mathbb{R}^N$ be open and $1 \le p < \infty$. Then: (a) the
conclusion of Corollary 9.14 holds for $W_0^{1,p}(\Omega)$
(`Brezis.Chapter09.remark_9_20_embedding`); (b) if $\Omega$ is bounded, the conclusion of
Theorem 9.16 holds for $W_0^{1,p}(\Omega)$ (`Brezis.Chapter09.remark_9_20_compact`); (c) if
$1 \le p < N$, there is $C$ with $\|u\|_{L^{p^*}(\Omega)} \le C \|\nabla u\|_{L^p(\Omega)}$ for
all $u \in W_0^{1,p}(\Omega)$ (`Brezis.Chapter09.remark_9_20_sobolev`).

**Reading.** The cases $p = N$ assume $N \ge 2$, and the constants may depend on $\Omega$; see
the three parts. -/
theorem remark_9_20 :
    ((∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ → p ≤ q →
        q ≤ p' → IsContinuousInjectionLpZero N p q Ω) ∧
      (2 ≤ N → p = (N : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
        IsContinuousInjectionLpZero N p q Ω) ∧
      ((N : ℝ≥0) < p → IsContinuousInjectionLpZero N p ⊤ Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ u : sobolevZeroSpace N p Ω, ∃ ũ : 𝔼 → ℝ,
          ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
          SobolevMultiIndex.fn (u : sobolevSpace N p Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧
          (∀ x ∈ closure (Ω : Set 𝔼), ∀ y ∈ closure (Ω : Set 𝔼),
            |ũ x - ũ y| ≤ C * bookNorm (u : sobolevSpace N p Ω)
              * ‖x - y‖ ^ (1 - (N : ℝ) / p)) ∧
          ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼), ∀ᵐ y ∂volume.restrict (Ω : Set 𝔼),
            |SobolevMultiIndex.fn (u : sobolevSpace N p Ω) x
                - SobolevMultiIndex.fn (u : sobolevSpace N p Ω) y|
              ≤ C * bookNorm (u : sobolevSpace N p Ω) * ‖x - y‖ ^ (1 - (N : ℝ) / p))) ∧
    (∀ hb : Bornology.IsBounded (Ω : Set 𝔼),
      (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ → q < p' →
        IsCompactInjectionLpZero N p q Ω) ∧
      (2 ≤ N → p = (N : ℝ≥0) → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], p ≤ q →
        IsCompactInjectionLpZero N p q Ω) ∧
      (∀ hp : (N : ℝ≥0) < p,
        haveI : CompactSpace (closure (Ω : Set 𝔼)) :=
          isCompact_iff_compactSpace.1 hb.isCompact_closure
        IsCompactEmbedding (toContinuousMapClosureZero hb hp).toLinearMap) ∧
      IsCompactInjectionLpZero N p p Ω) ∧
    (∀ (p' : ℝ≥0) [Fact (1 ≤ (p' : ℝ≥0∞))], p < N → (p' : ℝ)⁻¹ = p⁻¹ - (N : ℝ)⁻¹ →
      ∃ C : ℝ≥0, ∀ u ∈ sobolevZeroSpace N p Ω,
        eLpNorm (SobolevMultiIndex.fn u) p' (volume.restrict (Ω : Set 𝔼))
          ≤ C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))) :=
  ⟨remark_9_20_embedding, remark_9_20_compact, fun _ _ hpN hp' ↦ remark_9_20_sobolev hpN hp'⟩

end Remark20

/-! ### The gradient norm at $p = 2$ -/

section GradientTwo

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Let $u \in H^1(\Omega)$. Then
$$\|\nabla u\|_{L^2(\Omega)}^2 = \sum_{i=1}^N \Big\|\frac{\partial u}{\partial
  x_i}\Big\|_{L^2(\Omega)}^2.$$

The proof specializes `SobolevMultiIndex.eLpNorm_gradFn_two_sq`; `Brezis.Chapter09.gradient u`
is `SobolevMultiIndex.gradFn u`. -/
theorem eLpNorm_gradient_two_sq (u : hSpace N Ω) :
    eLpNorm (gradient u) 2 (volume.restrict (Ω : Set 𝔼)) ^ 2
      = ∑ i, eLpNorm (partialDeriv u i) 2 (volume.restrict (Ω : Set 𝔼)) ^ 2 :=
  SobolevMultiIndex.eLpNorm_gradFn_two_sq u

/-- Let $u \in H^1(\Omega)$. The $\ell^2$ gradient norm $(\sum_i \|\partial u / \partial
x_i\|_2^2)^{1/2}$ of the backbone equals $\|\nabla u\|_{L^2(\Omega)} = (\int_\Omega |\nabla
u|^2)^{1/2}$.

The $\ell^2$ gradient norm is `SobolevMultiIndex.gradNorm`. The proof specializes
`SobolevMultiIndex.gradNorm_eq_toReal_eLpNorm_gradFn`. -/
theorem gradNorm_eq_toReal_eLpNorm_gradient_two (u : hSpace N Ω) :
    SobolevMultiIndex.gradNorm u
      = (eLpNorm (gradient u) 2 (volume.restrict (Ω : Set 𝔼))).toReal :=
  SobolevMultiIndex.gradNorm_eq_toReal_eLpNorm_gradFn u

end GradientTwo

/-! ### Corollary 9.19: Poincaré's inequality -/

section Poincare

variable {d : ℕ}

/-- The space $\mathbb{R}^N$, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Corollary 9.19** of [brezis2011functional] (Poincaré's inequality). Let $N \ge 1$,
$1 \le p < \infty$, and let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set. There is a
constant $C \ge 0$, depending on $\Omega$ and $p$, such that
$$\|u\|_{L^p(\Omega)} \le C \|\nabla u\|_{L^p(\Omega)} \quad \text{for all } u \in
  W_0^{1,p}(\Omega).$$

The source gives no proof here. The proof specializes
`SobolevEuclideanZero.eLpNorm_fn_le_of_isBounded`, by the fundamental theorem of calculus and
Fubini's theorem along the last coordinate. It gives $C = 2R$ for $\Omega \subseteq B(0, R)$,
with $\|\partial u / \partial x_N\|_p$ in place of $\|\nabla u\|_p$. Here $N = d + 1$; for
$N = 0$ the inequality fails, since the constant function $1$ on the one-point space lies in
$W_0^{1,p}$ and has gradient $0$. -/
theorem corollary_9_19 (hp' : p ≠ ⊤) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ sobolevZeroSpace (d + 1) p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼))
        ≤ ENNReal.ofReal C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  refine ⟨2 * max R 0, by positivity, fun u hu ↦ ?_⟩
  refine (SobolevEuclideanZero.eLpNorm_fn_le_of_isBounded hp' (le_max_right R 0)
    (hR.trans (ball_subset_ball (le_max_left R 0))) ⟨u, hu⟩).trans ?_
  exact mul_le_mul' le_rfl (eLpNorm_partialDeriv_le u (Fin.last d))

/-- **Corollary 9.19** of [brezis2011functional], the norm statement for the $\ell^p$ gradient norm.
Let $1 \le p < \infty$ and let $\Omega$ be a bounded open set. There is a constant $C$ with
$$\|u\| \le C \Big(\sum_{i=1}^N \Big\|\frac{\partial u}{\partial x_i}\Big\|_p^p\Big)^{1/p} \quad
  \text{for all } u \in W_0^{1,p}(\Omega).$$
Thus the $\ell^p$ gradient norm is a norm on $W_0^{1,p}(\Omega)$ that is equivalent to $\|u\|$.

The $\ell^p$ gradient norm is `SobolevMultiIndex.gradNorm`. Its other norm axioms hold on all of
$W^{1,p}(\Omega)$ (`SobolevMultiIndex.gradNorm_add_le`, `SobolevMultiIndex.gradNorm_smul`), and
the other bound is `SobolevMultiIndex.gradNorm_le_norm`. The proof specializes
`SobolevEuclideanZero.norm_le_gradNorm`. -/
theorem corollary_9_19_gradNorm (hp' : p ≠ ⊤) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ C : ℝ, ∀ u ∈ sobolevZeroSpace (d + 1) p Ω, ‖u‖ ≤ C * SobolevMultiIndex.gradNorm u := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  exact ⟨_, fun u hu ↦ SobolevEuclideanZero.norm_le_gradNorm hp' (le_max_right R 0)
    (hR.trans (ball_subset_ball (le_max_left R 0))) ⟨u, hu⟩⟩

/-- **Corollary 9.19** of [brezis2011functional], "in particular, the expression
$\|\nabla u\|_{L^p(\Omega)}$ is a norm on $W_0^{1,p}(\Omega)$, and it is equivalent to the norm
$\|u\|_{W^{1,p}}$". Let $1 \le p < \infty$ and let $\Omega$ be a bounded open set. There are
constants $C_1 > 0$ and $C_2$ with
$$C_1 \|u\|_{W^{1,p}} \le \|\nabla u\|_{L^p(\Omega)} \le C_2 \|u\|_{W^{1,p}} \quad \text{for all
  } u \in W_0^{1,p}(\Omega).$$

In particular $\|\nabla u\|_{L^p(\Omega)} = 0$ forces $u = 0$
(`Brezis.Chapter09.corollary_9_19_norm_eq_zero`). The proof combines
`Brezis.Chapter09.corollary_9_19_gradNorm` with the comparison of the two gradient norms
(`Brezis.Chapter09.gradNorm_le_eLpNorm_gradient`,
`Brezis.Chapter09.toReal_eLpNorm_gradient_le_gradNorm`) and of the two norms of $W^{1,p}$
(`Brezis.Chapter09.bookNorm_equiv`). -/
theorem corollary_9_19_norm (hp' : p ≠ ⊤) (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ ∀ u ∈ sobolevZeroSpace (d + 1) p Ω,
      C₁ * bookNorm u ≤ (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal ∧
      (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal ≤ C₂ * bookNorm u := by
  obtain ⟨K, hK⟩ := corollary_9_19_gradNorm hp' hb
  set M : ℝ := ((d + 1 : ℕ) + 1) * max K 1 * (d + 1 : ℕ) with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M⁻¹, ((d + 1 : ℕ) : ℝ), inv_pos.2 hM0, fun u hu ↦ ⟨?_, ?_⟩⟩
  · rw [inv_mul_le_iff₀ hM0, hM]
    have h1 := (bookNorm_equiv u).2
    have h2 := hK u hu
    have h3 := gradNorm_le_eLpNorm_gradient u
    have h4 := SobolevMultiIndex.gradNorm_nonneg u
    have h5 : 0 ≤ (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal :=
      ENNReal.toReal_nonneg
    have hK1 : K ≤ max K 1 := le_max_left _ _
    have hK0 : 0 ≤ max K 1 := le_max_of_le_right zero_le_one
    calc bookNorm u ≤ ((d + 1 : ℕ) + 1) * ‖u‖ := h1
      _ ≤ ((d + 1 : ℕ) + 1) * (max K 1 * SobolevMultiIndex.gradNorm u) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_right hK1 h4)
      _ ≤ ((d + 1 : ℕ) + 1) * (max K 1 * ((d + 1 : ℕ)
            * (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal)) := by
          gcongr
      _ = _ := by ring
  · calc (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal
        ≤ (d + 1 : ℕ) * SobolevMultiIndex.gradNorm u := toReal_eLpNorm_gradient_le_gradNorm u
      _ ≤ (d + 1 : ℕ) * bookNorm u := by
          gcongr
          exact (SobolevMultiIndex.gradNorm_le_norm u).trans (bookNorm_equiv u).1

/-- **Corollary 9.19** of [brezis2011functional], definiteness of $\|\nabla u\|_{L^p(\Omega)}$. Let
$1 \le p < \infty$, let $\Omega$ be a bounded open set, and let $u \in W_0^{1,p}(\Omega)$ with
$\|\nabla u\|_{L^p(\Omega)} = 0$. Then $u = 0$. -/
theorem corollary_9_19_norm_eq_zero (hp' : p ≠ ⊤) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {u : sobolevSpace (d + 1) p Ω} (hu : u ∈ sobolevZeroSpace (d + 1) p Ω)
    (h : eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) = 0) : u = 0 := by
  obtain ⟨C₁, C₂, hC₁, hC⟩ := corollary_9_19_norm hp' hb
  have h1 := (hC u hu).1
  rw [h, ENNReal.toReal_zero] at h1
  have h2 : bookNorm u ≤ 0 := by nlinarith [bookNorm_nonneg u]
  exact (bookNorm_eq_zero_iff u).1 (le_antisymm h2 (bookNorm_nonneg u))

/-- **Corollary 9.19** of [brezis2011functional], last clause: the scalar product of
$H_0^1(\Omega)$. Let $\Omega$ be a bounded open set, and let $a(u, v)$ be the Dirichlet form on
$H^1(\Omega)$. Then: (a) $a(u, v) = \sum_i \int_\Omega \frac{\partial u}{\partial x_i}
\frac{\partial v}{\partial x_i}$ for all $u, v \in H^1(\Omega)$; (b) $a(u, v) = a(v, u)$ for all
$u, v \in H^1(\Omega)$; (c) $\sqrt{a(u, u)} = \|\nabla u\|_{L^2(\Omega)}$ for all
$u \in H^1(\Omega)$; (d) $a(u, u) > 0$ for every $u \in H_0^1(\Omega)$ with $u \ne 0$; (e) there
are constants $C_1 > 0$ and $C_2$ with $C_1 \|u\| \le \sqrt{a(u, u)} \le C_2 \|u\|$ for all
$u \in H_0^1(\Omega)$. Thus $a$ is a scalar product on $H_0^1(\Omega)$ whose norm
$\|\nabla u\|_{L^2(\Omega)}$ is equivalent to the norm of $H^1$.

The Dirichlet form is `Elliptic.dirichletForm Ω`, a bounded bilinear form on $H^1(\Omega)$.
Parts (d) and (e) follow from Poincaré's inequality (`SobolevEuclideanZero.norm_le_gradNorm` at
$p = 2$) and `Elliptic.dirichletForm_self_eq_gradNorm_sq`. -/
theorem corollary_9_19_inner (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    (∀ u v : hSpace (d + 1) Ω, Elliptic.dirichletForm Ω u v
        = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv u i x * partialDeriv v i x) ∧
    (∀ u v : hSpace (d + 1) Ω, Elliptic.dirichletForm Ω u v = Elliptic.dirichletForm Ω v u) ∧
    (∀ u : hSpace (d + 1) Ω, √(Elliptic.dirichletForm Ω u u)
        = (eLpNorm (gradient u) 2 (volume.restrict (Ω : Set 𝔼))).toReal) ∧
    (∀ u ∈ hZeroSpace (d + 1) Ω, u ≠ 0 → 0 < Elliptic.dirichletForm Ω u u) ∧
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ ∀ u ∈ hZeroSpace (d + 1) Ω,
      C₁ * ‖u‖ ≤ √(Elliptic.dirichletForm Ω u u) ∧
        √(Elliptic.dirichletForm Ω u u) ≤ C₂ * ‖u‖ := by
  have hsq : ∀ u : hSpace (d + 1) Ω,
      √(Elliptic.dirichletForm Ω u u) = SobolevMultiIndex.gradNorm u := fun u ↦ by
    rw [Elliptic.dirichletForm_self_eq_gradNorm_sq,
      Real.sqrt_sq (SobolevMultiIndex.gradNorm_nonneg u)]
  obtain ⟨K, hK⟩ := corollary_9_19_gradNorm (p := 2) (by simp) hb
  have hK0 : 0 < max K 1 := lt_max_of_lt_right zero_lt_one
  refine ⟨fun u v ↦ ?_, fun u v ↦ ?_, fun u ↦ ?_, fun u hu hu0 ↦ ?_,
    (max K 1)⁻¹, 1, inv_pos.2 hK0, fun u hu ↦ ⟨?_, ?_⟩⟩
  · rw [Elliptic.dirichletForm_apply_inner]
    exact Finset.sum_congr rfl fun i _ ↦ MeasureTheory.L2.inner_eq_integral_mul _ _
  · have h := Elliptic.dirichletForm_isHermitian Ω u v
    simpa using h
  · rw [hsq, gradNorm_eq_toReal_eLpNorm_gradient_two]
  · rw [Elliptic.dirichletForm_self_eq_gradNorm_sq]
    have h1 := hK u hu
    have h2 : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have h3 : 0 < SobolevMultiIndex.gradNorm u := by
      by_contra h
      push Not at h
      have := le_antisymm h (SobolevMultiIndex.gradNorm_nonneg u)
      rw [this, mul_zero] at h1
      exact absurd (h1.trans_lt' h2) (lt_irrefl _)
    positivity
  · rw [hsq, inv_mul_le_iff₀ hK0]
    exact (hK u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (SobolevMultiIndex.gradNorm_nonneg u))
  · rw [hsq, one_mul]
    exact SobolevMultiIndex.gradNorm_le_norm u

/-- **Remark 21** of Chapter 9 of [brezis2011functional], the bounded-projection clause. Let
$1 \le p < \infty$, $a, b \in \mathbb{R}$, and assume $a < x_N < b$ for all $x \in \Omega$. Then
$$\|u\|_{L^p(\Omega)} \le (b - a) \|\nabla u\|_{L^p(\Omega)} \quad \text{for all } u \in
  W_0^{1,p}(\Omega).$$

**Reading.** The source assumes that $\Omega$ has a bounded projection on some axis. The
statement here takes the last coordinate axis; the other axes follow by relabelling the
coordinates.

The proof specializes `SobolevEuclideanZero.eLpNorm_fn_le_of_subset_slab`, by the fundamental
theorem of calculus and Fubini's theorem along $x_N$. -/
theorem remark_9_21_projection (hp' : p ≠ ⊤) {a b : ℝ}
    (hΩ : ∀ x ∈ (Ω : Set 𝔼), a < x (Fin.last d) ∧ x (Fin.last d) < b) :
    ∀ u ∈ sobolevZeroSpace (d + 1) p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼))
        ≤ ENNReal.ofReal (b - a) * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  intro u hu
  rcases (Ω : Set 𝔼).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp only [h, Measure.restrict_empty, eLpNorm_measure_zero, zero_le]
  · have hab : a ≤ b := ((hΩ x hx).1.trans (hΩ x hx).2).le
    refine (SobolevEuclideanZero.eLpNorm_fn_le_of_subset_slab hp' hab
      (fun y hy ↦ hΩ y hy) ⟨u, hu⟩).trans ?_
    exact mul_le_mul' le_rfl (eLpNorm_partialDeriv_le u (Fin.last d))

end Poincare

section Remark21

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Remark 21** of Chapter 9 of [brezis2011functional], the finite-measure clause. Let $N \ge 2$,
$1 \le p < \infty$, and let $\Omega$ have finite measure. There is a constant $C < \infty$ with
$$\|u\|_{L^p(\Omega)} \le C \|\nabla u\|_{L^p(\Omega)} \quad \text{for all } u \in
  W_0^{1,p}(\Omega).$$

**Reading.** The source states the clause without a condition on $N$. The statement assumes
$N \ge 2$, which the proof through the Sobolev inequality needs.

The proof specializes `SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_measure_ne_top`. It uses
the Sobolev inequality of Remark 20, $W_0^{1,r}(\Omega) \subset L^{r^*}(\Omega)$ for some
$r \le p$ with $r < N$ and $r^* \ge p$, and Hölder's inequality on the set of finite measure. -/
theorem remark_9_21_measure (hp' : p ≠ ⊤) (hN : 2 ≤ N) (hΩ : volume (Ω : Set 𝔼) ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u ∈ sobolevZeroSpace N p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼))
        ≤ C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  obtain ⟨C, hC, h⟩ := SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_measure_ne_top
    (Ω := Ω) hp' hN hΩ
  refine ⟨C * N, ENNReal.mul_ne_top hC (ENNReal.natCast_ne_top N), fun u hu ↦ ?_⟩
  refine (h ⟨u, hu⟩).trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  have h1 := gradNorm_le_eLpNorm_gradient u
  have hfin : eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) ≠ ⊤ :=
    (memLp_gradient u).eLpNorm_ne_top
  calc ENNReal.ofReal (SobolevMultiIndex.gradNorm u)
      ≤ ENNReal.ofReal (N * (eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼))).toReal) :=
        ENNReal.ofReal_le_ofReal h1
    _ = N * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_toReal hfin]

end Remark21

section Remark21Both

variable {d : ℕ}

/-- The space $\mathbb{R}^N$, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Remark 21** of Chapter 9 of [brezis2011functional]. Let $1 \le p < \infty$. Assume that
$N \ge 2$ and $\Omega$ has finite measure, or that $a < x_N < b$ on $\Omega$ for some
$a, b \in \mathbb{R}$. Then Poincaré's inequality holds: there is a constant $C < \infty$ with
$$\|u\|_{L^p(\Omega)} \le C \|\nabla u\|_{L^p(\Omega)} \quad \text{for all } u \in
  W_0^{1,p}(\Omega).$$

**Reading.** The finite-measure clause assumes $N \ge 2$, and the bounded-projection clause uses
the last axis; see `Brezis.Chapter09.remark_9_21_measure` and
`Brezis.Chapter09.remark_9_21_projection`. -/
theorem remark_9_21 (hp' : p ≠ ⊤)
    (h : (1 ≤ d ∧ volume (Ω : Set 𝔼) ≠ ⊤) ∨
      ∃ a b : ℝ, ∀ x ∈ (Ω : Set 𝔼), a < x (Fin.last d) ∧ x (Fin.last d) < b) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u ∈ sobolevZeroSpace (d + 1) p Ω,
      eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼))
        ≤ C * eLpNorm (gradient u) p (volume.restrict (Ω : Set 𝔼)) := by
  rcases h with ⟨hd, hΩ⟩ | ⟨a, b, hΩ⟩
  · exact remark_9_21_measure hp' (by omega) hΩ
  · exact ⟨ENNReal.ofReal (b - a), ENNReal.ofReal_ne_top, remark_9_21_projection hp' hΩ⟩

end Remark21Both

/-! ### Remark 22: the spaces $W_0^{m,p}(\Omega)$ -/

section Higher

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of $\mathbb{R}^N$, as a basis of the module. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **Remark 22** of Chapter 9 of [brezis2011functional], the space $W_0^{m,p}(\Omega)$. Let
$m \in \mathbb{N}$, $1 \le p \le \infty$ and $\Omega \subseteq \mathbb{R}^N$ open. The space
**$W_0^{m,p}(\Omega)$** is the closure of the test functions $\mathcal{D}(\Omega)$ in
$W^{m,p}(\Omega)$, as a submodule of $W^{m,p}(\Omega)$.

The source defines $W_0^{m,p}(\Omega)$, for $m \ge 1$ and $1 \le p < \infty$, as the closure of
$C_c^m(\Omega)$ in $W^{m,p}(\Omega)$. The two closures agree by
`Brezis.Chapter09.sobolevZeroSpaceHigher_eq_closure_contDiff`. The definition is the backbone's
`SobolevEuclideanZero N m p Ω`. The heuristic of the remark, "$D^\alpha u = 0$ on $\Gamma$ for
$|\alpha| \le m - 1$", and its comparison of $W_0^{m,p}(\Omega)$ with
$W^{m,p}(\Omega) \cap W_0^{1,p}(\Omega)$ for $m \ge 2$ are not formalized. -/
noncomputable abbrev sobolevZeroSpaceHigher (N m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Submodule ℝ (sobolevSpaceHigher N m p Ω) :=
  SobolevEuclideanZero N m p Ω

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The space $W_0^{1,p}(\Omega)$ is the case $m = 1$ of $W_0^{m,p}(\Omega)$. -/
theorem sobolevZeroSpaceHigher_one :
    sobolevZeroSpaceHigher N 1 p Ω = sobolevZeroSpace N p Ω :=
  rfl

/-- **Remark 22** of Chapter 9 of [brezis2011functional], the definition through $C_c^m(\Omega)$.
Let $m \in \mathbb{N}$ and $1 \le p < \infty$. The closure in $W^{m,p}(\Omega)$ of the functions
that are a.e. on $\Omega$ equal to a $C^m$ function with compact support in $\Omega$ is
$W_0^{m,p}(\Omega)$.

As in Remark 18, the inclusion $\subseteq$ is Lemma 9.5 at order $m$
(`SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset`), and the inclusion $\supseteq$
holds because a test function is a $C^m$ function with compact support in $\Omega$. -/
theorem sobolevZeroSpaceHigher_eq_closure_contDiff (hp' : p ≠ ⊤) {m : ℕ} :
    closure {u : sobolevSpaceHigher N m p Ω | ∃ v : 𝔼 → ℝ, ContDiff ℝ m v ∧ HasCompactSupport v ∧
        tsupport v ⊆ Ω ∧ SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v}
      = (sobolevZeroSpaceHigher N m p Ω : Set (sobolevSpaceHigher N m p Ω)) := by
  apply subset_antisymm
  · refine closure_minimal ?_ SobolevMultiIndexZero.isClosed
    rintro u ⟨v, hv, hvc, hvΩ, hu⟩
    exact SobolevMultiIndex.mem_zero_of_fn_ae_eq_of_tsupport_subset hp' u hvc hvΩ hu
  · rw [show (sobolevZeroSpaceHigher N m p Ω : Set (sobolevSpaceHigher N m p Ω))
        = closure (SobolevMultiIndex.testFunctions ℝ 𝔟 m p Ω volume :
          Set (sobolevSpaceHigher N m p Ω)) from Submodule.topologicalClosure_coe _]
    refine closure_mono ?_
    rintro u ⟨φ, hφ⟩
    exact ⟨φ, φ.contDiff.of_le (by simp), φ.hasCompactSupport, φ.tsupport_subset, hφ⟩

end Higher

/-! ### The dual space of $W_0^{1,p}(\Omega)$ -/

section Dual

variable {N : ℕ}

/-- The space $\mathbb{R}^N$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of $\mathbb{R}^N$, as a basis of the module. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **Section 9.4** of [brezis2011functional], the dual space, Notation. Let $1 \le p \le \infty$
with conjugate exponent $p'$. The space **$W^{-1,p'}(\Omega)$** is the dual space of
$W_0^{1,p}(\Omega)$, the space of bounded linear functionals on $W_0^{1,p}(\Omega)$.

The source uses the notation for $1 \le p < \infty$. The dual norm is taken with respect to the
norm of the Lean type of $W_0^{1,p}(\Omega)$. -/
noncomputable abbrev dualSpace (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  StrongDual ℝ (sobolevZeroSpace N p Ω)

/-- **Section 9.4** of [brezis2011functional], the dual space, Notation. The space
**$H^{-1}(\Omega)$** is the dual space of $H_0^1(\Omega)$.

The source writes: "The dual of $L^2(\Omega)$ is identified with $L^2(\Omega)$, but we do not
identify $H_0^1(\Omega)$ with its dual." -/
noncomputable abbrev hMinusOne (N : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Type :=
  dualSpace N 2 Ω

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Section 9.4** of [brezis2011functional], the inclusions $H_0^1(\Omega) \subset L^2(\Omega)
\subset H^{-1}(\Omega)$, "where these injections are continuous and dense". Let
$\Omega \subseteq \mathbb{R}^N$ be open. The bounded linear map $H_0^1(\Omega) \to L^2(\Omega)$,
$u \mapsto u$, is injective with dense range. The bounded linear map
$L^2(\Omega) \to H^{-1}(\Omega)$ that sends $f$ to the functional $v \mapsto \int_\Omega f v$ is
injective with dense range.

The first map is the backbone's `SobolevMultiIndexZero.fnL`, and the second is
`SobolevEuclideanZero.toDualL2`. The proof specializes `SobolevEuclideanZero.gelfandTriple`. -/
theorem dual_inclusions :
    (∀ u : hZeroSpace N Ω, (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u : 𝔼 → ℝ)
        = SobolevMultiIndex.fn (u : hSpace N Ω)) ∧
      Function.Injective (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) ∧
      DenseRange (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) ∧
    (∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (v : hZeroSpace N Ω),
        (SobolevEuclideanZero.toDualL2 N Ω f : hMinusOne N Ω) v
          = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v : hSpace N Ω) x) ∧
      Function.Injective (SobolevEuclideanZero.toDualL2 N Ω) ∧
      DenseRange (SobolevEuclideanZero.toDualL2 N Ω) :=
  ⟨fun u ↦ SobolevMultiIndexZero.fnL_apply u, SobolevEuclideanZero.gelfandTriple.1,
    SobolevEuclideanZero.gelfandTriple.2.1, fun f v ↦ SobolevEuclideanZero.toDualL2_apply f v,
    SobolevEuclideanZero.gelfandTriple.2.2.1, SobolevEuclideanZero.gelfandTriple.2.2.2⟩

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Proposition 9.20** of [brezis2011functional]. Let $1 \le p < \infty$ with conjugate exponent
$p'$, and let $F \in W^{-1,p'}(\Omega)$. Then there are functions
$f_0, f_1, \dots, f_N \in L^{p'}(\Omega)$ such that
$$\langle F, v \rangle = \int_\Omega f_0 v + \sum_{i=1}^N \int_\Omega f_i \frac{\partial
  v}{\partial x_i} \quad \text{for all } v \in W_0^{1,p}(\Omega),$$
and $\|f_i\|_{L^{p'}(\Omega)} \le \|F\|$ for every $i = 0, 1, \dots, N$.

**Reading.** The source states $\|F\| = \max_{0 \le i \le N} \|f_i\|_{p'}$. This identity refers
to the norm $\sum_i \|h_i\|_p$ on $(L^p)^{N+1}$. For the $\ell^p$ norm of the Lean type the
identity takes another form, and only the bound is stated.

The proof specializes `SobolevEuclideanZero.exists_dual_repr`. As the source says, it adapts the
proof of Proposition 8.14: the Hahn–Banach theorem on the $\ell^p$ product of $N + 1$ copies of
$L^p(\Omega)$ and the Riesz representation theorem on each factor. The sum over multi-indices
splits into the index $0$ and the $N$ unit indices. -/
theorem proposition_9_20 [p.HolderConjugate q] (hp' : p ≠ ⊤) (F : dualSpace N p Ω) :
    ∃ (f₀ : Lp ℝ q (volume.restrict (Ω : Set 𝔼)))
      (f : Fin N → Lp ℝ q (volume.restrict (Ω : Set 𝔼))),
      (∀ v : sobolevZeroSpace N p Ω,
        F v = (∫ x in (Ω : Set 𝔼), f₀ x * SobolevMultiIndex.fn (v : sobolevSpace N p Ω) x)
          + ∑ i, ∫ x in (Ω : Set 𝔼), f i x * partialDeriv (v : sobolevSpace N p Ω) i x) ∧
      ‖f₀‖ ≤ ‖F‖ ∧ ∀ i, ‖f i‖ ≤ ‖F‖ := by
  obtain ⟨f, hf, hfn⟩ := SobolevEuclideanZero.exists_dual_repr (q := q) hp' F
  refine ⟨f 0, fun i ↦ f (MultiIndexLE.single i), fun v ↦ ?_, hfn 0, fun i ↦ hfn _⟩
  rw [hf v, MultiIndexLE.sum_univ_one]
  rfl

end Dual

section DualBounded

variable {d : ℕ}

/-- The space $\mathbb{R}^N$, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Proposition 9.20** of [brezis2011functional], last sentence: "if $\Omega$ is bounded we can
take $f_0 = 0$". Let $1 \le p < \infty$ with conjugate exponent $p'$, and let $\Omega$ be a
bounded open set. There is a constant $C$ such that every $F \in W^{-1,p'}(\Omega)$ has
functions $f_1, \dots, f_N \in L^{p'}(\Omega)$ with
$$\langle F, v \rangle = \sum_{i=1}^N \int_\Omega f_i \frac{\partial v}{\partial x_i} \quad
  \text{for all } v \in W_0^{1,p}(\Omega)$$
and $\|f_i\|_{L^{p'}(\Omega)} \le C \|F\|$ for every $i$.

The constant comes from Poincaré's inequality, by which $v \mapsto \nabla v$ is bounded below on
$W_0^{1,p}(\Omega)$. The proof specializes `SobolevEuclideanZero.exists_dual_repr_of_isBounded`. -/
theorem proposition_9_20_bounded [p.HolderConjugate q] (hp' : p ≠ ⊤)
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ C : ℝ, ∀ F : dualSpace (d + 1) p Ω, ∃ f : Fin (d + 1) → Lp ℝ q (volume.restrict (Ω : Set 𝔼)),
      (∀ v : sobolevZeroSpace (d + 1) p Ω,
        F v = ∑ i, ∫ x in (Ω : Set 𝔼), f i x * partialDeriv (v : sobolevSpace (d + 1) p Ω) i x) ∧
      ∀ i, ‖f i‖ ≤ C * ‖F‖ := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  refine ⟨(1 + (2 * max R 0) ^ p.toReal) ^ (1 / p.toReal), fun F ↦ ?_⟩
  obtain ⟨f, hf, hfn⟩ := SobolevEuclideanZero.exists_dual_repr_of_isBounded (q := q) hp'
    (le_max_right R 0) (hR.trans (ball_subset_ball (le_max_left R 0))) F
  exact ⟨f, hf, hfn⟩

end DualBounded

section DualLe

variable {d : ℕ}

/-- The space $\mathbb{R}^N$, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The standard basis of $\mathbb{R}^N$, as a basis of the module. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

variable {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The inclusion $W_0^{1,p}(\Omega) \subset L^2(\Omega)$. Let $1 < p < \infty$ with
$2N/(N + 2) \le p$, and assume $p \le 2$ or $\Omega$ bounded. There is a bounded linear map
$\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ such that $\iota v = v$ a.e. on $\Omega$ for every
$v \in W_0^{1,p}(\Omega)$.

For $p \le 2$ the map is the embedding $W_0^{1,p}(\Omega) \subset L^q(\Omega)$ of Remark 20 at
$q = 2$ (`Brezis.Chapter09.remark_9_20_embedding`), since the condition $1/p - 1/N \le 1/2$ is
$2N/(N + 2) \le p$. For $p > 2$ and bounded $\Omega$ it is the inclusion $W_0^{1,p}(\Omega)
\subset W_0^{1,2}(\Omega) \subset L^2(\Omega)$ (`SobolevMultiIndexZero.toLowerExponentL`), by
Hölder's inequality on a set of finite measure. -/
theorem exists_inclusionL2_of_le (hp : 1 < p)
    (hpN : (2 * (d + 1 : ℕ) / ((d + 1 : ℕ) + 2) : ℝ) ≤ p)
    (h : p ≤ 2 ∨ Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ ι : sobolevZeroSpace (d + 1) p Ω →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
      ∀ v : sobolevZeroSpace (d + 1) p Ω, (ι v : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)]
        SobolevMultiIndex.fn (v : sobolevSpace (d + 1) p Ω) := by
  rcases le_or_gt p 2 with hp2 | hp2
  · -- `p ≤ 2`: Remark 20 at `q = 2`
    have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans (by exact_mod_cast hp)
    have hN0 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
    have hq : (p : ℝ)⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ ≤ ((2 : ℝ≥0) : ℝ)⁻¹ := by
      rw [div_le_iff₀ (by positivity)] at hpN
      rw [NNReal.coe_ofNat, sub_le_iff_le_add, inv_eq_one_div, inv_eq_one_div, inv_eq_one_div,
        div_add_div _ _ two_ne_zero hN0.ne', div_le_div_iff₀ hp0 (by positivity)]
      nlinarith
    refine ⟨(SobolevEuclideanZero.isContinuousEmbedding_toLp (q := 2) (Or.inr hp) hp2
      hq).toContinuousLinearMap, fun v ↦ ?_⟩
    exact SobolevMultiIndex.toLpₗOn_coeFn _ v
  · -- `p > 2`, `Ω` bounded: `W_0^{1,p}(Ω) ⊂ W_0^{1,2}(Ω) ⊂ L²(Ω)`
    have hb : Bornology.IsBounded (Ω : Set 𝔼) := h.resolve_left (not_le.2 hp2)
    have h2p : (2 : ℝ≥0∞) ≤ p := by exact_mod_cast hp2.le
    refine ⟨(SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume).comp
      (SobolevMultiIndexZero.toLowerExponentL ℝ 𝔟 1 p 2 volume hb.measure_lt_top.ne h2p),
      fun v ↦ ?_⟩
    rw [ContinuousLinearMap.comp_apply, SobolevMultiIndexZero.fnL_apply]
    exact SobolevMultiIndexZero.fn_toLowerExponentL hb.measure_lt_top.ne h2p v

/-- **Section 9.4** of [brezis2011functional], the dual space, the inclusions $W_0^{1,p}(\Omega)
\subset L^2(\Omega) \subset W^{-1,p'}(\Omega)$. Let $1 < p < \infty$ with $2N/(N + 2) \le p$,
and assume $p \le 2$ or $\Omega$ bounded. There is a bounded linear map
$\iota : W_0^{1,p}(\Omega) \to L^2(\Omega)$ with $\iota v = v$ a.e. on $\Omega$, and $\iota$ is
injective with dense range. The map $L^2(\Omega) \to W^{-1,p'}(\Omega)$ that sends $f$ to the
functional $v \mapsto \int_\Omega f v$ is also injective with dense range.

**Correction.** The source states that if $\Omega$ is bounded, then $W_0^{1,p}(\Omega) \subset
L^2(\Omega) \subset W^{-1,p'}(\Omega)$ with continuous and dense injections for
$2N/(N + 2) \le p < \infty$, and that for unbounded $\Omega$ the same holds for
$2N/(N + 2) \le p \le 2$. This range contains $p = 1$ when $N \le 2$. There the density of
$L^2(\Omega)$ in $W^{-1,\infty}(\Omega)$ fails: $W_0^{1,1}(\Omega)$ contains a complemented copy
of $\ell^1$, so its dual is not separable. The statement here assumes $p > 1$.

The map $\iota$ is `Brezis.Chapter09.exists_inclusionL2_of_le`, and the second map is
`SobolevEuclideanZero.toDualOfL2 ι`, the transpose of $\iota$ composed with the identification
of $L^2(\Omega)$ with its dual. The proof specializes
`SobolevEuclideanZero.gelfandTriple_of_forall_ae_eq`; the density of the second map follows from
the reflexivity of $W_0^{1,p}(\Omega)$. -/
theorem dual_inclusions_of_le (hp : 1 < p)
    (hpN : (2 * (d + 1 : ℕ) / ((d + 1 : ℕ) + 2) : ℝ) ≤ p)
    (h : p ≤ 2 ∨ Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ ι : sobolevZeroSpace (d + 1) p Ω →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
      (∀ v : sobolevZeroSpace (d + 1) p Ω, (ι v : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)]
        SobolevMultiIndex.fn (v : sobolevSpace (d + 1) p Ω)) ∧
      Function.Injective ι ∧ DenseRange ι ∧
      (∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (v : sobolevZeroSpace (d + 1) p Ω),
        (SobolevEuclideanZero.toDualOfL2 ι f : dualSpace (d + 1) p Ω) v
          = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v : sobolevSpace (d + 1) p Ω) x) ∧
      Function.Injective (SobolevEuclideanZero.toDualOfL2 ι) ∧
      DenseRange (SobolevEuclideanZero.toDualOfL2 ι) := by
  refine (exists_inclusionL2_of_le hp hpN h).imp fun ι hι ↦ ?_
  have hp1 : (1 : ℝ≥0∞) < p := by exact_mod_cast hp
  have hp' : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have h4 := SobolevEuclideanZero.gelfandTriple_of_forall_ae_eq hp1 hp' hι
  exact ⟨hι, h4.1, h4.2.1, fun f v ↦ SobolevEuclideanZero.toDualOfL2_apply hι f v, h4.2.2.1,
    h4.2.2.2⟩

end DualLe

end Brezis.Chapter09
