/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Boundary.ChartGraph
import Numlib.Analysis.Sobolev.Extension
import NumlibSurface.Brezis.Chapter09.Section01

/-!
# Brezis, Section 9.2: Extension operators

This module formalizes Section 9.2 of [brezis2011functional]. An open set
$\Omega \subseteq \mathbb{R}^N$ is of class $C^1$ if near each point of its boundary
$\Gamma = \partial\Omega$ there is a $C^1$ chart $H$ from the cylinder $Q$ that maps the upper half
$Q_+$ onto the part of $\Omega$ and the equator $Q_0$ onto the part of $\Gamma$. For such an
$\Omega$ with bounded boundary, and for the half space $\mathbb{R}^N_+$, there is a bounded linear
extension operator $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ (Theorem 9.7). The proof extends
a function on $Q_+$ to $Q$ by reflection (Lemma 9.2) and glues the local extensions with a partition
of unity (Lemma 9.3). As a consequence, the restrictions to $\Omega$ of the functions of
$C_c^\infty(\mathbb{R}^N)$ are dense in $W^{1,p}(\Omega)$ for $1 \le p < \infty$ (Corollary 9.8).

The proofs specialize the backbone modules `Numlib.Analysis.Sobolev.Chart`,
`Numlib.Analysis.Sobolev.Reflection`, `Numlib.Analysis.Sobolev.Extension` and
`Numlib.Analysis.Sobolev.Boundary.ChartGraph`.

## Main definitions

* Section 9.2, definition of an open set of class $C^m$, `Brezis.Chapter09.IsOfClassC`: an open set
  with a local chart of class $C^m$ at each boundary point, unfolded by
  `Brezis.Chapter09.isOfClassC_iff`.
* Section 9.2, definition of an open set of class $C^1$, `Brezis.Chapter09.IsClassC1`: the case
  $m = 1$.

## Main results

* `Brezis.Chapter09.isClassC1_iff_isContDiffDomain`: an open set is of class $C^1$ in the sense of
  the source if and only if it is a $C^1$ domain in the sense of local graphs; the two directions
  are `Brezis.Chapter09.isClassC1_of_isContDiffDomain` and
  `Brezis.Chapter09.isContDiffDomain_of_isClassC1`.
* Theorem 9.7, `Brezis.Chapter09.theorem_9_7`: an extension operator
  $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ for $\Omega$ of class $C^1$ with bounded boundary;
  the case of the half space is `Brezis.Chapter09.theorem_9_7_halfSpace`.
* Lemma 9.2, `Brezis.Chapter09.lemma_9_2`: the extension by reflection $u^\star$ of
  $u \in W^{1,p}(Q_+)$ lies in $W^{1,p}(Q)$, with the identities (7) and (8) and the constant $2$;
  the case of the half space is `Brezis.Chapter09.lemma_9_2_halfSpace`.
* Remark 9, `Brezis.Chapter09.remark_9_9`: an extension operator for the square $(0, 1)^2$, which is
  not of class $C^1$.
* Lemma 9.3, `Brezis.Chapter09.lemma_9_3`: a smooth partition of unity subordinate to an open
  covering of a compact set $\Gamma$.
* Corollary 9.8, `Brezis.Chapter09.corollary_9_8`: for $\Omega$ of class $C^1$ and
  $1 \le p < \infty$, every $u \in W^{1,p}(\Omega)$ is a limit of restrictions of functions of
  $C_c^\infty(\mathbb{R}^N)$; the density form is `Brezis.Chapter09.corollary_9_8_dense`, and the
  proof through Theorem 9.7 for a bounded boundary is `Brezis.Chapter09.corollary_9_8_bounded`.

## Conventions

* The dimension is written $N = d + 1$, because the section singles out the last coordinate $x_N$.
  The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin (d + 1))`, a point is $x = (x', x_N)$, and
  $e_N$ is `EuclideanSpace.single (Fin.last d) 1`.
* The half space $\mathbb{R}^N_+ = \{x_N > 0\}$ is `EuclideanSpace.upperHalfSpace d`. The cylinder
  $Q = \{|x'| < 1, |x_N| < 1\}$ is `unitChartCube d`, $Q_+ = Q \cap \mathbb{R}^N_+$ is
  `unitChartCubePos d`, and $Q_0 = \{(x', 0) : |x'| < 1\}$ is `unitChartCubeZero d`.
* As open sets, $Q$ is `unitChartCubeOpens d` and $Q_+$ is `posHalf e_N Q`, whose underlying set is
  `unitChartCubePos d` (`coe_posHalf_unitChartCubeOpens`). The half space is `posHalf e_N ⊤`, whose
  underlying set is `EuclideanSpace.upperHalfSpace d` (`coe_posHalf_top_eq_upperHalfSpace`).
* The extension by reflection $u^\star$ of Lemma 9.2 is `evenReflection e_N u`, and the odd
  reflection $f^\square$ of its proof is `oddReflection e_N f`.
* The norm $\|\cdot\|_{W^{1,p}}$ of the source is `Brezis.Chapter09.bookNorm`.

## Implementation notes

* "$\Omega$ is of class $C^1$" is `Brezis.Chapter09.IsClassC1 Ω`, the definition of the source by
  local charts $H : Q \to U$. It is the backbone's `IsContDiffChartDomain 1 Ω`. The definition by
  local graphs of Definition 7.2.1 of [han2009theoretical], `IsContDiffDomain 1 Ω`, is equivalent to
  it: a local graph gives a local chart by straightening (`IsContDiffDomain.isContDiffChartDomain`),
  and the implicit function theorem gives the converse (`IsContDiffChartDomain.isContDiffDomain`).

## Deviations from the source

* **Definition of an open set of class $C^\infty$** (reading). The source defines "of class
  $C^\infty$" as "of class $C^m$ for every $m$". The library reads it as one chart of class
  $C^\infty$ at each boundary point, which is a priori stronger. See `Brezis.Chapter09.IsOfClassC`.
-/

open Filter MeasureTheory Metric Topology TopologicalSpace EuclideanSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

namespace Brezis.Chapter09

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The last basis vector $e_N$ of $\mathbb{R}^N$, the normal of the hyperplane $x_N = 0$. -/
local notation "eN" => EuclideanSpace.single (Fin.last d) (1 : ℝ)

/-! ### Open sets of class $C^m$ -/

/-- **Section 9.2** of [brezis2011functional], definition of an open set of class $C^m$. An open set
$\Omega \subseteq \mathbb{R}^N$ with boundary $\Gamma = \partial\Omega$ is **of class $C^m$** if
for every $x \in \Gamma$ there are a neighbourhood $U$ of $x$ in $\mathbb{R}^N$ and a bijective
map $H : Q \to U$ such that
$$H \in C^m(\bar Q), \quad H^{-1} \in C^m(\bar U), \quad H(Q_+) = U \cap \Omega, \quad H(Q_0) =
  U \cap \Gamma.$$

**Reading.** The source defines "of class $C^\infty$" as "of class $C^m$ for every $m$". Here
`IsOfClassC ⊤ Ω` asks for one chart of class $C^\infty$ at each boundary point, which is a
priori stronger, and which is what the regularity theorems of Section 9.6 and Chapter 10 use.
The implicit function theorem (`IsContDiffChartDomain.isContDiffDomain`, for every order
$m \ge 1$ other than the analytic order $\omega$) turns a chart of class $C^m$ into a graph, so
`IsOfClassC m Ω` for every $m$ gives `IsContDiffDomain m Ω` for every $m \ge 1$. The uniform
statement, one $C^\infty$ graph function for every order, needs the graph function to be the
same for all $m$, and is not proved.

The source states the definition for $m = 1$ in Section 9.2 and for general $m$ in Section 9.6.
The definition is the backbone's chart condition `IsContDiffChartDomain m Ω`, and
`Brezis.Chapter09.isOfClassC_iff` unfolds it to the wording of the source. Here $m$ ranges over
$\mathbb{N} \cup \{\infty\}$. -/
def IsOfClassC (m : ℕ∞) (Ω : Set 𝔼) : Prop :=
  IsContDiffChartDomain m Ω

/-- **Section 9.2** of [brezis2011functional], definition of an open set of class $C^m$, unfolded to
the wording of the source. Let $m \ge 0$ be an integer. An open set
$\Omega \subseteq \mathbb{R}^N$ is of class $C^m$ if and only if $\Omega$ is open and for every
$x \in \partial\Omega$ there are an open neighbourhood $U$ of $x$ and a map $H : Q \to U$, a
bijection with inverse $H^{-1}$, such that $H \in C^m(\bar Q)$, $H^{-1} \in C^m(\bar U)$,
$H(Q_+) = U \cap \Omega$ and $H(Q_0) = U \cap \partial\Omega$.

The maps $H$ and $H^{-1}$ are functions on $\mathbb{R}^N$. The regularity on the closures is
`ContDiffOn` on `closure (unitChartCube d)` and on `closure U`, and the bijection is `Set.BijOn`
with inverse `Set.InvOn` between $Q$ and $U$. -/
theorem isOfClassC_iff (m : ℕ) (Ω : Set 𝔼) :
    IsOfClassC m Ω ↔ IsOpen Ω ∧ ∀ x ∈ frontier Ω, ∃ (U : Set 𝔼) (H Hinv : 𝔼 → 𝔼),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ m H (closure (unitChartCube d)) ∧
      ContDiffOn ℝ m Hinv (closure U) ∧ Set.BijOn H (unitChartCube d) U ∧
      Set.InvOn Hinv H (unitChartCube d) U ∧ H '' unitChartCubePos d = U ∩ Ω ∧
      H '' unitChartCubeZero d = U ∩ frontier Ω := by
  constructor
  · rintro ⟨hΩ, h⟩
    refine ⟨hΩ, fun x hx ↦ ?_⟩
    obtain ⟨c, hc⟩ := h x hx
    exact ⟨c.U, c.toFun, c.invFun, c.isOpen_U, hc, c.contDiffOn, c.contDiffOn_invFun, c.bijOn,
      c.invOn, c.image_pos, c.image_zero⟩
  · rintro ⟨hΩ, h⟩
    refine ⟨hΩ, fun x hx ↦ ?_⟩
    obtain ⟨U, H, Hinv, hU, hxU, hH, hHinv, hbij, hinv, hpos, hzero⟩ := h x hx
    exact ⟨⟨U, H, Hinv, hU, hH, hHinv, hbij, hinv, hpos, hzero⟩, hxU⟩

/-- An open set of class $C^m$ is of class $C^k$ for every $k \le m$. -/
theorem IsOfClassC.of_le {m k : ℕ∞} {Ω : Set 𝔼} (h : IsOfClassC m Ω) (hkm : k ≤ m) :
    IsOfClassC k Ω :=
  IsContDiffChartDomain.of_le h (by exact_mod_cast hkm)

/-- An open set of class $C^m$ is open. -/
theorem IsOfClassC.isOpen {m : ℕ∞} {Ω : Set 𝔼} (h : IsOfClassC m Ω) : IsOpen Ω :=
  h.1

/-- **Section 9.2** of [brezis2011functional], definition of an open set of class $C^1$. An open set
$\Omega$ is **of class $C^1$** if it is of class $C^m$ for $m = 1$
(`Brezis.Chapter09.IsOfClassC`).

This is the hypothesis of Theorem 9.7 and Corollary 9.8, and of Corollaries 9.14 and 9.15,
Theorem 9.16 and Remark 21 in Sections 9.3 and 9.4 of the source. -/
abbrev IsClassC1 (Ω : Set 𝔼) : Prop :=
  IsOfClassC 1 Ω

/-- The two definitions of a $C^1$ domain agree, one direction. A $C^1$ domain in the sense of local
graphs, `IsContDiffDomain 1 Ω` (Definition 7.2.1 of [han2009theoretical]), is of class $C^1$ in
the sense of [brezis2011functional], Section 9.2.

A local graph gives a local chart by straightening (`IsContDiffDomain.isContDiffChartDomain`).
The converse is `Brezis.Chapter09.isContDiffDomain_of_isClassC1`. -/
theorem isClassC1_of_isContDiffDomain {Ω : Set 𝔼} (h : IsContDiffDomain 1 Ω) : IsClassC1 Ω :=
  h.isContDiffChartDomain

/-- The two definitions of a $C^1$ domain agree, the other direction. An open set of class $C^1$ in
the sense of the source, by local charts, is a $C^1$ domain in the sense of local graphs,
`IsContDiffDomain 1 Ω` (Definition 7.2.1 of [han2009theoretical]).

The proof specializes the backbone's `IsContDiffChartDomain.isContDiffDomain`: the implicit
function theorem applies to the last coordinate of the inverse chart, whose derivative is
invertible, after a rigid motion that sends its gradient to $e_N$. -/
theorem isContDiffDomain_of_isClassC1 {Ω : Set 𝔼} (h : IsClassC1 Ω) : IsContDiffDomain 1 Ω :=
  h.isContDiffDomain le_rfl WithTop.coe_ne_top

/-- The two definitions of a $C^1$ domain agree. An open set $\Omega$ is of class $C^1$ in the sense
of the source, by local charts, if and only if it is a $C^1$ domain in the sense of local
graphs, `IsContDiffDomain 1 Ω` (Definition 7.2.1 of [han2009theoretical]). -/
theorem isClassC1_iff_isContDiffDomain {Ω : Set 𝔼} : IsClassC1 Ω ↔ IsContDiffDomain 1 Ω :=
  ⟨isContDiffDomain_of_isClassC1, isClassC1_of_isContDiffDomain⟩

/-! ### Theorem 9.7 -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and $1 \le p \le \infty$. Suppose that there are a
bounded linear operator $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ and a constant $C$ such
that, for every $u \in W^{1,p}(\Omega)$, $Pu = u$ almost everywhere on $\Omega$,
$\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\Omega)}$ and $\|Pu\| \le C \|u\|$ for the norm of
the type. Then there are such $P$ and $C$ with the last bound for the norm of the source:
$\|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}(\Omega)}$.

This converts the backbone form of Theorem 9.7 of [brezis2011functional] to the norm
`Brezis.Chapter09.bookNorm` of the source, through the equivalence of the two norms. -/
theorem exists_extension_of_backbone {Ω : Opens 𝔼}
    (h : ∃ (P : sobolevSpace (d + 1) p Ω →L[ℝ] sobolevSpace (d + 1) p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict Ω) ∧
        ‖P u‖ ≤ C * ‖u‖) :
    ∃ (P : sobolevSpace (d + 1) p Ω →L[ℝ] sobolevSpace (d + 1) p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict Ω) ∧
        bookNorm (P u) ≤ C * bookNorm u := by
  obtain ⟨P, C, hP⟩ := h
  refine ⟨P, ((d + 1 : ℕ) + 1) * max C 0, fun u ↦ ⟨(hP u).1, ?_, ?_⟩⟩
  · refine (hP u).2.1.trans ?_
    gcongr
    calc C ≤ max C 0 := le_max_left _ _
      _ = 1 * max C 0 := (one_mul _).symm
      _ ≤ ((d + 1 : ℕ) + 1) * max C 0 :=
          mul_le_mul_of_nonneg_right (by norm_cast; omega) (le_max_right _ _)
  · calc bookNorm (P u) ≤ ((d + 1 : ℕ) + 1) * ‖P u‖ := (bookNorm_equiv (P u)).2
      _ ≤ ((d + 1 : ℕ) + 1) * (C * ‖u‖) :=
          mul_le_mul_of_nonneg_left (hP u).2.2 (by positivity)
      _ ≤ ((d + 1 : ℕ) + 1) * (max C 0 * bookNorm u) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc C * ‖u‖ ≤ max C 0 * ‖u‖ :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
            _ ≤ max C 0 * bookNorm u :=
                mul_le_mul_of_nonneg_left (bookNorm_equiv u).1 (le_max_right _ _)
      _ = ((d + 1 : ℕ) + 1) * max C 0 * bookNorm u := by ring

/-- **Theorem 9.7** of [brezis2011functional]. Suppose that $\Omega$ is of class $C^1$ with
$\Gamma = \partial\Omega$ bounded, and let $1 \le p \le \infty$. Then there are a bounded linear
extension operator $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ and a constant $C$ such that
for all $u \in W^{1,p}(\Omega)$:

(i) $Pu|_\Omega = u$;

(ii) $\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\Omega)}$;

(iii) $\|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}(\Omega)}$.

The source says that $C$ depends only on $\Omega$; here $C$ depends on $\Omega$ and $p$.
Property (i) holds almost everywhere on $\Omega$, and the norm in (iii) is the norm
`Brezis.Chapter09.bookNorm` of the source. -/
theorem theorem_9_7 {Ω : Opens 𝔼} (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    ∃ (P : sobolevSpace (d + 1) p Ω →L[ℝ] sobolevSpace (d + 1) p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict Ω) ∧
        bookNorm (P u) ≤ C * bookNorm u :=
  exists_extension_of_backbone (SobolevEuclidean.exists_extensionL hΩ hΓ)

/-- **Theorem 9.7** of [brezis2011functional], the case of the half space $\Omega = \mathbb{R}^N_+$.
Let $1 \le p \le \infty$. There are a bounded linear extension operator $P :
W^{1,p}(\mathbb{R}^N_+) \to W^{1,p}(\mathbb{R}^N)$ and a constant $C$ such that for all
$u \in W^{1,p}(\mathbb{R}^N_+)$, $Pu = u$ almost everywhere on $\mathbb{R}^N_+$,
$\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\mathbb{R}^N_+)}$ and
$\|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}(\mathbb{R}^N_+)}$.

The operator is the extension by reflection of Lemma 9.2. The half space is
`EuclideanSpace.upperHalfSpaceOpens d`. -/
theorem theorem_9_7_halfSpace :
    ∃ (P : sobolevSpace (d + 1) p (upperHalfSpaceOpens d) →L[ℝ] sobolevSpace (d + 1) p ⊤)
      (C : ℝ), ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (upperHalfSpace d)]
          SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C
            * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d)) ∧
        bookNorm (P u) ≤ C * bookNorm u :=
  exists_extension_of_backbone SobolevEuclidean.exists_extensionL_upperHalfSpace

/-- **Remark 9** in Chapter 9 of [brezis2011functional]. Lemma 9.2 gives a simple construction of
extension operators for some open sets that are not of class $C^1$. Let $\Omega = \{x \in
\mathbb{R}^2 : 0 < x_1 < 1, \ 0 < x_2 < 1\}$ be the square and $1 \le p \le \infty$. There are a
bounded linear extension operator $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^2)$ and a constant
$C$ such that for all $u \in W^{1,p}(\Omega)$, $Pu = u$ almost everywhere on $\Omega$,
$\|Pu\|_{L^p(\mathbb{R}^2)} \le C \|u\|_{L^p(\Omega)}$ and $\|Pu\|_{W^{1,p}(\mathbb{R}^2)} \le C
\|u\|_{W^{1,p}(\Omega)}$.

The square is `EuclideanSpace.rect 0 1 0 1`. The construction is that of the source: four
successive reflections (Figure 6) give $\tilde u \in W^{1,p}(\tilde\Omega)$ with
$\tilde\Omega = (-1, 3)^2$, followed by a cut-off. The proof specializes
`SobolevEuclidean.exists_extensionL_unitSquare`. -/
theorem remark_9_9 :
    ∃ (P : sobolevSpace 2 p (EuclideanSpace.rect 0 1 0 1) →L[ℝ] sobolevSpace 2 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u)
          =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))]
            SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        bookNorm (P u) ≤ C * bookNorm u :=
  exists_extension_of_backbone (d := 1) SobolevEuclidean.exists_extensionL_unitSquare

/-! ### Lemma 9.2 -/

/-- Let $\sigma$ be the reflection across the hyperplane $x_N = 0$, let $w : \mathbb{R}^N \to
\mathcal{L}(\mathbb{R}^N, \mathbb{R})$, and let $i = 1, \dots, N$. For every $x$, the reflected
derivative of $w$ at $x$ (`reflectFDeriv e_N w x`), applied to $e_i$, has the same absolute
value as the even reflection of the function $z \mapsto w(z) e_i$ at $x$.

The reflection $\sigma$ fixes the vectors $e_i$ with $i < N$ and sends $e_N$ to $-e_N$. This
supports the norm bounds of Lemma 9.2 of [brezis2011functional]. -/
theorem norm_reflectFDeriv_single (w : 𝔼 → 𝔼 →L[ℝ] ℝ) (x : 𝔼) (i : Fin (d + 1)) :
    ‖reflectFDeriv eN w x (EuclideanSpace.single i 1)‖
      = ‖evenReflection eN (fun z ↦ w z (EuclideanSpace.single i 1)) x‖ := by
  by_cases hx : 0 ≤ ⟪x, eN⟫_ℝ
  · rw [reflectFDeriv_of_nonneg _ hx, evenReflection_of_nonneg _ hx]
  · rw [reflectFDeriv_of_neg _ (not_le.1 hx), evenReflection_of_neg _ (not_le.1 hx),
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    by_cases hi : i = Fin.last d
    · subst hi
      rw [hyperplaneReflection_apply_self, map_neg, norm_neg]
    · have h2 : ⟪(EuclideanSpace.single i (1 : ℝ) : 𝔼), eN⟫_ℝ = 0 := by
        rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
        simp [hi]
      rw [hyperplaneReflection_apply_of_inner_eq_zero _ h2]

/-- Let $V \subseteq \mathbb{R}^N$ be open and invariant under the reflection across $x_N = 0$, and
let $V_+ = V \cap \{x_N > 0\}$. If $f = g$ almost everywhere on $V_+$, then
$f^\square = g^\square$ almost everywhere on $V$, where $f^\square$ is the odd reflection of $f$
(`oddReflection e_N f`). -/
theorem oddReflection_congr_ae {V : Opens 𝔼} (hV : hyperplaneReflection eN '' (V : Set 𝔼) = V)
    {f g : 𝔼 → ℝ} (h : f =ᵐ[volume.restrict (posHalf eN V : Set 𝔼)] g) :
    oddReflection eN f =ᵐ[volume.restrict (V : Set 𝔼)] oddReflection eN g := by
  have hv0 : (eN : 𝔼) ≠ 0 :=
    ne_zero_of_norm_ne_zero (by rw [norm_single_last_one]; exact one_ne_zero)
  filter_upwards [evenReflection_congr_ae hv0 hV h] with x hx
  simp only [evenReflection, oddReflection] at hx ⊢
  split_ifs at hx ⊢ with h0
  · exact hx
  · rw [hx]

/-- **Lemma 9.2** of [brezis2011functional], for an open set symmetric under the reflection across
$x_N = 0$. Let $V \subseteq \mathbb{R}^N$ be open and invariant under this reflection, let
$V_+ = V \cap \{x_N > 0\}$, and let $1 \le p \le \infty$ and $u \in W^{1,p}(V_+)$. Then the
extension by reflection $u^\star$ lies in $W^{1,p}(V)$, with
$$\|u^\star\|_{L^p(V)} \le 2 \|u\|_{L^p(V_+)}, \qquad
  \|u^\star\|_{W^{1,p}(V)} \le 2 \|u\|_{W^{1,p}(V_+)},$$
and, almost everywhere on $V$,
$$\frac{\partial u^\star}{\partial x_i} = \Big(\frac{\partial u}{\partial x_i}\Big)^\star
  \text{ for } 1 \le i \le N - 1 \quad (7), \qquad
  \frac{\partial u^\star}{\partial x_N} = \Big(\frac{\partial u}{\partial x_N}\Big)^\square
  \quad (8).$$

The norm $\|\cdot\|_{W^{1,p}}$ is `Brezis.Chapter09.bookNorm`. The cases $V = Q$ and
$V = \mathbb{R}^N$ are `Brezis.Chapter09.lemma_9_2` and `Brezis.Chapter09.lemma_9_2_halfSpace`. -/
theorem lemma_9_2_of_symm {V : Opens 𝔼} (hV : hyperplaneReflection eN '' (V : Set 𝔼) = V)
    (u : sobolevSpace (d + 1) p (posHalf eN V)) :
    ∃ w : sobolevSpace (d + 1) p V,
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (V : Set 𝔼)]
        evenReflection eN (SobolevMultiIndex.fn u) ∧
      eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict V)
        ≤ 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (posHalf eN V)) ∧
      bookNorm w ≤ 2 * bookNorm u ∧
      (∀ i : Fin d, partialDeriv w i.castSucc =ᵐ[volume.restrict (V : Set 𝔼)]
        evenReflection eN (partialDeriv u i.castSucc)) ∧
      partialDeriv w (Fin.last d) =ᵐ[volume.restrict (V : Set 𝔼)]
        oddReflection eN (partialDeriv u (Fin.last d)) := by
  have hv : ‖(eN : 𝔼)‖ = 1 := norm_single_last_one
  have hv0 : (eN : 𝔼) ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨W, hW, hWp, hWi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  -- the reflected element, with its specification and the operator forgotten
  obtain ⟨w, hw1, hw2, hwd⟩ : ∃ w : sobolevSpace (d + 1) p V,
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (V : Set 𝔼)]
        evenReflection eN (SobolevMultiIndex.fn u) ∧
      eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict V)
        ≤ 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (posHalf eN V)) ∧
      ∀ i, partialDeriv w i =ᵐ[volume.restrict (V : Set 𝔼)]
        fun x ↦ reflectFDeriv eN W x (EuclideanSpace.single i 1) := by
    refine ⟨SobolevEuclidean.evenReflectionL hv hV u, SobolevMultiIndex.fn_evenReflectionL hv hV u,
      SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le hv hV u, fun i ↦ ?_⟩
    have := SobolevMultiIndex.weakDeriv_evenReflection_single hv hV u hW hWp i
    rwa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] at this
  refine ⟨w, hw1, hw2, ?_, ?_, ?_⟩
  -- the book's norm: each partial derivative of `w` is bounded by twice the one of `u`
  · have hle : ∀ i, ‖partialDeriv w i‖ ≤ 2 * ‖partialDeriv u i‖ := fun i ↦ by
      have hm1 : AEStronglyMeasurable (fun x ↦ reflectFDeriv eN W x (EuclideanSpace.single i 1))
          (volume.restrict (V : Set 𝔼)) :=
        (Lp.aestronglyMeasurable _).congr (hwd i)
      have hm2 : AEStronglyMeasurable (fun z ↦ W z (EuclideanSpace.single i 1))
          (volume.restrict (posHalf eN V : Set 𝔼)) :=
        (Lp.aestronglyMeasurable _).congr (hWi i).symm
      have h1 : eLpNorm (partialDeriv w i) p (volume.restrict (V : Set 𝔼))
          ≤ 2 * eLpNorm (partialDeriv u i) p (volume.restrict (posHalf eN V : Set 𝔼)) := by
        rw [eLpNorm_congr_ae (hwd i), eLpNorm_congr_norm_ae hm1
          (aestronglyMeasurable_evenReflection hv0 hV hm2)
          (Eventually.of_forall fun x ↦ norm_reflectFDeriv_single W x i),
          ← eLpNorm_congr_ae (hWi i)]
        exact eLpNorm_evenReflection_le hv0 hV hp hm2
      rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Lp.eLpNorm_ne_top _)) h1
    have h0 : ‖SobolevMultiIndex.weakDeriv w 0‖ ≤ 2 * ‖SobolevMultiIndex.weakDeriv u 0‖ := by
      rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Lp.eLpNorm_ne_top _)) hw2
    calc bookNorm w ≤ 2 * ‖SobolevMultiIndex.weakDeriv u 0‖ + ∑ i, 2 * ‖partialDeriv u i‖ :=
          add_le_add h0 (Finset.sum_le_sum fun i _ ↦ hle i)
      _ = 2 * bookNorm u := by rw [bookNorm, mul_add, Finset.mul_sum]
  -- (7): the tangential derivatives are even reflections
  · intro i
    have h2 : ⟪(EuclideanSpace.single i.castSucc (1 : ℝ) : 𝔼), eN⟫_ℝ = 0 := by
      rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
      simp [Fin.castSucc_ne_last]
    have h3 : (fun x ↦ reflectFDeriv eN W x (EuclideanSpace.single i.castSucc 1))
        =ᵐ[volume.restrict (V : Set 𝔼)]
          evenReflection eN (fun z ↦ W z (EuclideanSpace.single i.castSucc 1)) :=
      Eventually.of_forall fun x ↦ reflectFDeriv_apply_of_inner_eq_zero _ W h2 x
    exact (hwd i.castSucc).trans (h3.trans (evenReflection_congr_ae hv0 hV (hWi i.castSucc)))
  -- (8): the normal derivative is an odd reflection
  · have h3 : (fun x ↦ reflectFDeriv eN W x (EuclideanSpace.single (Fin.last d) 1))
        =ᵐ[volume.restrict (V : Set 𝔼)] oddReflection eN (fun z ↦ W z eN) :=
      Eventually.of_forall fun x ↦ reflectFDeriv_apply_self _ W x
    exact (hwd (Fin.last d)).trans (h3.trans (oddReflection_congr_ae hV (hWi (Fin.last d))))

/-- **Lemma 9.2** of [brezis2011functional]. Let $1 \le p \le \infty$ and $u \in W^{1,p}(Q_+)$. The
extension by reflection
$$u^\star(x', x_N) = \begin{cases} u(x', x_N) & \text{if } x_N > 0, \\
  u(x', -x_N) & \text{if } x_N < 0 \end{cases}$$
lies in $W^{1,p}(Q)$, with $\|u^\star\|_{L^p(Q)} \le 2 \|u\|_{L^p(Q_+)}$ and
$\|u^\star\|_{W^{1,p}(Q)} \le 2 \|u\|_{W^{1,p}(Q_+)}$. Moreover, almost everywhere on $Q$,
$$\frac{\partial u^\star}{\partial x_i} = \Big(\frac{\partial u}{\partial x_i}\Big)^\star
  \text{ for } 1 \le i \le N - 1 \quad (7), \qquad
  \frac{\partial u^\star}{\partial x_N} = \Big(\frac{\partial u}{\partial x_N}\Big)^\square
  \quad (8),$$
where $f^\square(x', x_N) = f(x', x_N)$ if $x_N > 0$ and $f^\square(x', x_N) = -f(x', -x_N)$ if
$x_N < 0$.

The extension $u^\star$ is `evenReflection e_N u`.
The odd reflection $f^\square$ is `oddReflection e_N f`.
Both take the value of the first case also on $x_N = 0$, a null set. The open set $Q_+$ is
`posHalf e_N Q`, whose underlying set is `unitChartCubePos d`. The norm $\|\cdot\|_{W^{1,p}}$ is
`Brezis.Chapter09.bookNorm`. -/
theorem lemma_9_2 (u : sobolevSpace (d + 1) p (posHalf eN (unitChartCubeOpens d))) :
    ∃ w : sobolevSpace (d + 1) p (unitChartCubeOpens d),
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (unitChartCube d)]
        evenReflection eN (SobolevMultiIndex.fn u) ∧
      eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (unitChartCube d))
        ≤ 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (unitChartCubePos d)) ∧
      bookNorm w ≤ 2 * bookNorm u ∧
      (∀ i : Fin d, partialDeriv w i.castSucc =ᵐ[volume.restrict (unitChartCube d)]
        evenReflection eN (partialDeriv u i.castSucc)) ∧
      partialDeriv w (Fin.last d) =ᵐ[volume.restrict (unitChartCube d)]
        oddReflection eN (partialDeriv u (Fin.last d)) := by
  have h := lemma_9_2_of_symm (p := p) hyperplaneReflection_image_unitChartCubeOpens u
  rwa [eLpNorm_restrict_congr_set_eq _ p coe_posHalf_unitChartCubeOpens] at h

/-- **Lemma 9.2** of [brezis2011functional], the case of the half space: "the conclusion of Lemma
9.2 remains valid if $Q_+$ is replaced by $\mathbb{R}^N_+$". Let $1 \le p \le \infty$ and
$u \in W^{1,p}(\mathbb{R}^N_+)$. Then $u^\star \in W^{1,p}(\mathbb{R}^N)$, with
$\|u^\star\|_{L^p(\mathbb{R}^N)} \le 2 \|u\|_{L^p(\mathbb{R}^N_+)}$,
$\|u^\star\|_{W^{1,p}(\mathbb{R}^N)} \le 2 \|u\|_{W^{1,p}(\mathbb{R}^N_+)}$, and the identities
(7) and (8) almost everywhere on $\mathbb{R}^N$.

Here $\mathbb{R}^N_+$ is `posHalf e_N ⊤`, whose underlying set is
`EuclideanSpace.upperHalfSpace d` (`coe_posHalf_top_eq_upperHalfSpace`). -/
theorem lemma_9_2_halfSpace (u : sobolevSpace (d + 1) p (posHalf eN ⊤)) :
    ∃ w : sobolevSpace (d + 1) p ⊤,
      SobolevMultiIndex.fn w =ᵐ[volume] evenReflection eN (SobolevMultiIndex.fn u) ∧
      eLpNorm (SobolevMultiIndex.fn w) p volume
        ≤ 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d)) ∧
      bookNorm w ≤ 2 * bookNorm u ∧
      (∀ i : Fin d, partialDeriv w i.castSucc =ᵐ[volume]
        evenReflection eN (partialDeriv u i.castSucc)) ∧
      partialDeriv w (Fin.last d) =ᵐ[volume] oddReflection eN (partialDeriv u (Fin.last d)) := by
  obtain ⟨w, h1, h2, h3, h4, h5⟩ :=
    lemma_9_2_of_symm (p := p) (hyperplaneReflection_image_top (eN : 𝔼)) u
  refine ⟨w, eventuallyEq_restrict_coe_top_iff.1 h1, ?_, h3,
    fun i ↦ eventuallyEq_restrict_coe_top_iff.1 (h4 i), eventuallyEq_restrict_coe_top_iff.1 h5⟩
  rwa [eLpNorm_restrict_coe_top,
    eLpNorm_restrict_congr_set_eq _ p coe_posHalf_top_eq_upperHalfSpace] at h2

/-! ### Lemma 9.3 and Corollary 9.8 -/

/-- **Lemma 9.3** of [brezis2011functional] (partition of unity). Let
$\Gamma \subseteq \mathbb{R}^N$ be compact and let $U_1, \dots, U_k$ be open sets that cover
$\Gamma$. Then there are functions $\theta_0, \theta_1, \dots, \theta_k \in
C^\infty(\mathbb{R}^N)$ such that

(i) $0 \le \theta_i \le 1$ for $i = 0, \dots, k$, and $\sum_{i=0}^k \theta_i = 1$ on
$\mathbb{R}^N$;

(ii) $\operatorname{supp} \theta_i$ is compact and $\operatorname{supp} \theta_i \subseteq U_i$
for $i = 1, \dots, k$, and $\operatorname{supp} \theta_0 \subseteq \mathbb{R}^N \setminus
\Gamma$;

(iii) if $\Omega$ is open and bounded with $\Gamma = \partial\Omega$, then
$\theta_0|_\Omega \in C_c^\infty(\Omega)$.

Property (iii) is stated as: the set $\operatorname{supp} \theta_0 \cap \bar\Omega$ is compact
and contained in $\Omega$. The same functions $\theta_i$ serve for every such $\Omega$. -/
theorem lemma_9_3 {Γ : Set 𝔼} (hΓ : IsCompact Γ) {k : ℕ} {U : Fin k → Set 𝔼}
    (hU : ∀ i, IsOpen (U i)) (hΓU : Γ ⊆ ⋃ i, U i) :
    ∃ (θ₀ : 𝔼 → ℝ) (θ : Fin k → 𝔼 → ℝ), ContDiff ℝ ∞ θ₀ ∧ (∀ i, ContDiff ℝ ∞ (θ i)) ∧
      (∀ x, θ₀ x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i x, θ i x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, θ₀ x + ∑ i, θ i x = 1) ∧ (∀ i, HasCompactSupport (θ i)) ∧
      (∀ i, tsupport (θ i) ⊆ U i) ∧ tsupport θ₀ ⊆ Γᶜ ∧
      ∀ Ω : Set 𝔼, IsOpen Ω → Bornology.IsBounded Ω → frontier Ω = Γ →
        IsCompact (tsupport θ₀ ∩ closure Ω) ∧ tsupport θ₀ ∩ closure Ω ⊆ Ω := by
  obtain ⟨θ₀, θ, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hΓ.exists_contDiff_partitionOfUnity hU hΓU
  refine ⟨θ₀, θ, h0, h1, h2, h3, h4, h5, h6, Set.disjoint_left.1 h7, fun Ω hΩ hΩb hΓΩ ↦
    ⟨(isClosed_tsupport θ₀).isCompact_inter_closure_of_isBounded hΩb,
      inter_closure_subset_of_disjoint_frontier hΩ (hΓΩ ▸ h7)⟩⟩

/-- **Corollary 9.8** of [brezis2011functional] (density). Let $\Omega$ be of class $C^1$,
$1 \le p < \infty$ and $u \in W^{1,p}(\Omega)$. Then there is a sequence $(u_n)$ of functions of
$C_c^\infty(\mathbb{R}^N)$ such that $u_n|_\Omega \to u$ in $W^{1,p}(\Omega)$: there are
elements $w_n \in W^{1,p}(\Omega)$ whose functions equal $u_n$ almost everywhere on $\Omega$,
and $w_n \to u$.

The boundary of $\Omega$ need not be bounded. -/
theorem corollary_9_8 {Ω : Opens 𝔼} (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤)
    (u : sobolevSpace (d + 1) p Ω) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      ∃ w : ℕ → sobolevSpace (d + 1) p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set 𝔼)] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto hp' hΩ u

/-- **Corollary 9.8** of [brezis2011functional], "in other words". Let $\Omega$ be of class $C^1$
and $1 \le p < \infty$. The restrictions to $\Omega$ of the functions of
$C_c^\infty(\mathbb{R}^N)$ form a dense subspace of $W^{1,p}(\Omega)$: the set of the elements
of $W^{1,p}(\Omega)$ whose function equals a function of $C_c^\infty(\mathbb{R}^N)$ almost
everywhere on $\Omega$ is dense. -/
theorem corollary_9_8_dense {Ω : Opens 𝔼} (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤) :
    Dense {w : sobolevSpace (d + 1) p Ω | ∃ v : 𝔼 → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)] v} := by
  intro u
  obtain ⟨v, hvs, hvc, w, hw, hwu⟩ := corollary_9_8 hΩ hp' u
  exact mem_closure_of_tendsto hwu (Eventually.of_forall fun n ↦ ⟨v n, hvs n, hvc n, hw n⟩)

/-- **Corollary 9.8** of [brezis2011functional], the case of a bounded boundary. Let $\Omega$ be of
class $C^1$ with $\Gamma = \partial\Omega$ bounded, $1 \le p < \infty$ and
$u \in W^{1,p}(\Omega)$. Then there is a sequence $(u_n)$ of functions of
$C_c^\infty(\mathbb{R}^N)$ such that $u_n|_\Omega \to u$ in $W^{1,p}(\Omega)$, in the sense of
`Brezis.Chapter09.corollary_9_8`.

The proof goes through the extension operator of Theorem 9.7, as in the first paragraph of the
proof of the source. -/
theorem corollary_9_8_bounded {Ω : Opens 𝔼} (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (hp' : p ≠ ⊤)
    (u : sobolevSpace (d + 1) p Ω) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      ∃ w : ℕ → sobolevSpace (d + 1) p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set 𝔼)] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_isBounded_frontier hp' hΩ hΓ u

end Brezis.Chapter09
