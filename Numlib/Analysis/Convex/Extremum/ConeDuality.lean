/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Extremum.Fenchel

/-!
# Duality between a co-finite function and a closed convex cone

Let $E$ and $F$ be finite-dimensional real normed spaces in duality through a pairing
$\langle x, y \rangle$. Let $h$ be a convex function on $E$ that is finite everywhere and co-finite,
let $K \subseteq E$ be a nonempty closed convex cone, and let $K^* = -K^\circ = \{y : \langle x, y
\rangle \ge 0 \text{ for all } x \in K\}$. Then for every $z \in E$ and $z^* \in F$,
$$\inf_{x \in K} \bigl\{ h(z + x) - \langle x, z^* \rangle \bigr\} + \inf_{x^* \in K^*} \bigl\{
  h^*(z^* + x^*) - \langle z, x^* \rangle \bigr\} = \langle z, z^* \rangle,$$
and both infima are finite and attained. This is a duality between $h$ and $h^*$ with one parameter
in each space. It is Corollary 31.4.3 of [rockafellar1970convex], and the proof uses the conjugacy
theory of §§12, 13 and 31 there.

The proof uses the auxiliary function $f(x) = h(z + x) - \langle x, z^* \rangle$. Its conjugate is
the dual objective minus the constant $\langle z, z^* \rangle$. Since $h$ is finite everywhere,
$\operatorname{dom} f = E$, and since $h$ is co-finite, $\operatorname{dom} f^* = F$. These are the
two constraint qualifications for the duality between a convex function and a cone, each in its
strongest form.

## Main results

* `ConvexAnalysis.iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing`: the duality identity above. This
  is Corollary 31.4.3 of [rockafellar1970convex].
* `ConvexAnalysis.exists_iInf_mem_eq_of_cofinite`,
  `ConvexAnalysis.exists_iInf_mem_neg_polarCone_eq_of_cofinite`: both infima are attained.
* `ConvexAnalysis.exists_iInf_mem_eq_coe_of_cofinite`,
  `ConvexAnalysis.exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite`: both infima are finite.

## Notation

* $K^\circ$: the polar cone `ConvexAnalysis.polarCone B K`, the set of $y$ with
  $\langle x, y \rangle \le 0$ for all $x \in K$. The dual cone $K^*$ is `-(polarCone B K)`.
* $\delta(\cdot \mid K)$: the indicator function `ConvexAnalysis.indicatorFn K`, which is $0$ on $K$
  and $+\infty$ off $K$.

## Implementation notes

* The pairing is `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, and both `B` and `B.flip` are
  `ConvexAnalysis.IsCompatiblePairing`. The point $z^*$ is `z'`.
* A cone is `ConvexAnalysis.IsCone`, a set closed under multiplication by positive scalars.
  Co-finiteness is `ConvexAnalysis.Cofinite`: $h$ is closed, proper and convex, and its recession
  function is $+\infty$ in every nonzero direction.
* The closedness of $K$ is used only for the attainment of the primal infimum, whose proof uses the
  bipolar identity $K^{\circ\circ} = K$. The identity, the finiteness of both infima and the
  attainment of the dual infimum need only that $K$ is a nonempty convex cone.
* Finite dimension is used only for two facts: a convex function that is finite everywhere is
  continuous, and a co-finite function has a conjugate that is finite everywhere.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### The translated, tilted function -/

section Shift

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {h : E → EReal}

/-- Let $h : E \to [-\infty, +\infty]$, $z \in E$ and $z^* \in F$. Then $h(z + x) - \langle x, z^*
\rangle = h(z + x) + r$ with the real number $r = -\langle x, z^* \rangle$, for every $x \in E$. -/
theorem comp_add_sub_pairing_eq_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (z : E) (z' : F) :
    (fun x => h (z + x) - ((B x z' : ℝ) : EReal))
      = fun x => h (z + x) + ((-(B x z') : ℝ) : EReal) := by
  funext x
  rw [EReal.coe_neg, ← sub_eq_add_neg]

/-- If $h$ is convex, then $f(x) = h(z + x) - \langle x, z^* \rangle$ is convex, since it is a
translate of $h$ plus a linear function. -/
theorem convexFn_comp_add_sub_pairing (hh : ConvexFn h) (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : E) (z' : F) :
    ConvexFn (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) := by
  rw [comp_add_sub_pairing_eq_add_coe]
  refine convexFn_add_coe (hh.comp_add_left z) fun x y a b _ => ?_
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- If $h$ is proper and finite everywhere, then $f(x) = h(z + x) - \langle x, z^* \rangle$ is a
real number for every $x \in E$. -/
theorem exists_comp_add_sub_pairing_eq_coe (hp : ProperConvex h) (hdom : convexDom h = univ)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : E) (z' : F) (x : E) :
    ∃ r : ℝ, h (z + x) - ((B x z' : ℝ) : EReal) = (r : EReal) := by
  obtain ⟨p, hp'⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot (z + x))
    (by rw [← mem_convexDom, hdom]; trivial)
  exact ⟨p - B x z', by rw [hp', ← EReal.coe_sub]⟩

/-- If $h$ is proper and finite everywhere, then $f(x) = h(z + x) - \langle x, z^* \rangle$ is
proper. -/
theorem properConvex_comp_add_sub_pairing (hp : ProperConvex h) (hdom : convexDom h = univ)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : E) (z' : F) :
    ProperConvex (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) := by
  refine ⟨⟨0, ?_⟩, fun x => ?_⟩
  · obtain ⟨r, hr⟩ := exists_comp_add_sub_pairing_eq_coe hp hdom B z z' 0
    rw [mem_convexDom, hr]
    exact EReal.coe_lt_top r
  · obtain ⟨r, hr⟩ := exists_comp_add_sub_pairing_eq_coe hp hdom B z z' x
    rw [hr]
    exact EReal.coe_ne_bot r

/-- If $h$ is proper and finite everywhere, then $f(x) = h(z + x) - \langle x, z^* \rangle$ is
finite everywhere: $\operatorname{dom} f = E$. -/
theorem convexDom_comp_add_sub_pairing_eq_univ (hp : ProperConvex h) (hdom : convexDom h = univ)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : E) (z' : F) :
    convexDom (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨r, hr⟩ := exists_comp_add_sub_pairing_eq_coe hp hdom B z z' x
  rw [mem_convexDom, hr]
  exact EReal.coe_lt_top r

/-- Let $f(x) = h(z + x) - \langle x, z^* \rangle$. Then the conjugate of $f$ is the dual objective
minus the constant $\langle z, z^* \rangle$: for every $w \in F$,
$$f^*(w) = \bigl( h^*(z^* + w) - \langle z, w \rangle \bigr) - \langle z, z^* \rangle.$$
-/
theorem convexConj_comp_add_sub_pairing_eq_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (z : E)
    (z' : F) (w : F) :
    convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w
      = (convexConj B h (z' + w) - ((B z w : ℝ) : EReal)) + ((-(B z z') : ℝ) : EReal) := by
  rw [convexConj_comp_add_sub_pairing, EReal.coe_neg, ← sub_eq_add_neg]

/-- Let $f(x) = h(z + x) - \langle x, z^* \rangle$ and $K^* = -K^\circ$. Then
$$\inf_{w \in K^*} f^*(w) = \inf_{w \in K^*} \bigl\{ h^*(z^* + w) - \langle z, w \rangle
  \bigr\} - \langle z, z^* \rangle.$$
The shift is a real constant, so it moves out of the infimum. -/
theorem iInf_mem_neg_polarCone_convexConj_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (K : Set E)
    (z : E) (z' : F) :
    (⨅ w ∈ -(polarCone B K), convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w)
      = (⨅ w ∈ -(polarCone B K), (convexConj B h (z' + w) - ((B z w : ℝ) : EReal)))
        + ((-(B z z') : ℝ) : EReal) := by
  rw [EReal.biInf_add_coe]
  exact iInf_congr fun w => iInf_congr fun _ => convexConj_comp_add_sub_pairing_eq_add_coe B
      h z z' w

end Shift

/-! ### The cone duality identity -/

section DualityIdentity

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
  {h : E → EReal} {K : Set E}

omit [FiniteDimensional ℝ E] in
/-- If $h$ is co-finite, then $h^*(z^* + w) - \langle z, w \rangle$ is a real number for all
$z \in E$ and $z^*, w \in F$, since $h^*$ is finite everywhere. -/
theorem exists_convexConj_comp_add_sub_pairing_eq_coe (hcof : Cofinite h) (z : E) (z' : F) (w : F) :
    ∃ r : ℝ, convexConj B h (z' + w) - ((B z w : ℝ) : EReal) = (r : EReal) := by
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (convexConj_ne_bot hcof.proper.convexDom_nonempty (z' + w))
    (by rw [← mem_convexDom, Cofinite.convexDom_convexConj_eq_univ (B := B) hcof]; trivial)
  exact ⟨s - B z w, by rw [hs, ← EReal.coe_sub]⟩

omit [FiniteDimensional ℝ E] in
/-- If $h$ is co-finite, then the conjugate of $f(x) = h(z + x) - \langle x, z^* \rangle$ is finite
everywhere: $\operatorname{dom} f^* = F$. -/
theorem convexDom_convexConj_comp_add_sub_pairing_eq_univ (hcof : Cofinite h) (z : E) (z' : F) :
    convexDom (convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal))) = univ := by
  refine eq_univ_of_forall fun w => ?_
  obtain ⟨r, hr⟩ := exists_convexConj_comp_add_sub_pairing_eq_coe (B := B) hcof z z' w
  rw [mem_convexDom, convexConj_comp_add_sub_pairing_eq_add_coe, hr, ← EReal.coe_add]
  exact EReal.coe_lt_top _

omit [FiniteDimensional ℝ F] [IsCompatiblePairing B.flip] in
/-- Let $h$ be co-finite and finite everywhere, and let $K$ be nonempty and convex. Then
$f(x) = h(z + x) - \langle x, z^* \rangle$ and the indicator function $\delta(\cdot \mid K)$ add
exactly: the conjugate of $f + \delta(\cdot \mid K)$ is the infimal convolution of their
conjugates, and the infimal convolution is attained.

The function $f$ is finite everywhere and hence continuous. This is the constraint qualification
on the primal side. Exact addition is `ConvexAnalysis.IsExactSum`. -/
theorem isExactSum_comp_add_sub_pairing_indicatorFn (hcof : Cofinite h) (hdom : convexDom h = univ)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (z : E) (z' : F) :
    IsExactSum B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) (indicatorFn K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hconvf := convexFn_comp_add_sub_pairing hcof.convex B z z'
  have hpf := properConvex_comp_add_sub_pairing hcof.proper hdom B z z'
  have hdomf := convexDom_comp_add_sub_pairing_eq_univ hcof.proper hdom B z z'
  refine IsExactSum.of_continuousAt hconvf hpf (convexFn_indicatorFn.2 hconv)
    ⟨⟨x₀, by rw [convexDom_indicatorFn]; exact hx₀⟩, indicatorFn_ne_bot K⟩
    (by rw [hdomf]; trivial) (by rw [convexDom_indicatorFn]; exact hx₀) ?_
  exact (hconvf.continuous_of_convexDom_eq_univ hpf hdomf).continuousAt

omit [FiniteDimensional ℝ E] in
/-- Let $h$ be co-finite and finite everywhere. Then the conjugate $f^*$ of
$f(x) = h(z + x) - \langle x, z^* \rangle$ and the indicator function $\delta(\cdot \mid K^*)$
of $K^* = -K^\circ$ add exactly, for the flipped pairing.

The function $f^*$ is finite everywhere because $h$ is co-finite. This is the constraint
qualification on the dual side. -/
theorem isExactSum_convexConj_comp_add_sub_pairing_indicatorFn (hcof : Cofinite h)
    (hdom : convexDom h = univ)
    (z : E) (z' : F) :
    IsExactSum B.flip (convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)))
      (indicatorFn (-(polarCone B K))) := by
  have hpf : ProperConvex (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) :=
    properConvex_comp_add_sub_pairing hcof.proper hdom B z z'
  have hdomc := convexDom_convexConj_comp_add_sub_pairing_eq_univ (B := B) hcof z z'
  have hpc : ProperConvex (convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal))) :=
    ⟨⟨0, by rw [hdomc]; trivial⟩, fun w => convexConj_ne_bot hpf.convexDom_nonempty w⟩
  refine IsExactSum.of_continuousAt (convexFn_convexConj B _) hpc
    (convexFn_indicatorFn.2 (convex_neg_polarCone B K))
    ⟨⟨0, by rw [convexDom_indicatorFn]; exact zero_mem_neg_polarCone B K⟩, indicatorFn_ne_bot _⟩
    (by rw [hdomc]; trivial)
    (by rw [convexDom_indicatorFn]; exact zero_mem_neg_polarCone B K) ?_
  exact ((convexFn_convexConj B _).continuous_of_convexDom_eq_univ hpc hdomc).continuousAt

omit [FiniteDimensional ℝ E] in
/-- If $h$ is co-finite, then $\inf_{w \in K^*} f^*(w) < +\infty$, where
$f(x) = h(z + x) - \langle x, z^* \rangle$ and $K^* = -K^\circ$. The origin lies in $K^*$, and
$f^*(0)$ is finite. -/
theorem iInf_mem_neg_polarCone_convexConj_ne_top (hcof : Cofinite h) (z : E) (z' : F) :
    (⨅ w ∈ -(polarCone B K),
      convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w) ≠ ⊤ := by
  have hdomc := convexDom_convexConj_comp_add_sub_pairing_eq_univ (B := B) hcof z z'
  have hlt : convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) 0 < ⊤ := by
    rw [← mem_convexDom, hdomc]; trivial
  have hge : (⨅ w ∈ -(polarCone B K),
        convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w)
      ≤ convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) 0 :=
    iInf₂_le (0 : F) (zero_mem_neg_polarCone B K)
  exact (lt_of_le_of_lt hge hlt).ne

omit [FiniteDimensional ℝ F] [IsCompatiblePairing B.flip] in
/-- Let $h$ be co-finite and finite everywhere, and let $K$ be a nonempty convex cone. Then
$\inf_{w \in K^*} f^*(w) > -\infty$, where $f(x) = h(z + x) - \langle x, z^* \rangle$ and
$K^* = -K^\circ$. Its negative is the primal infimum, which is at most a finite value. -/
theorem iInf_mem_neg_polarCone_convexConj_ne_bot (hcof : Cofinite h) (hdom : convexDom h = univ)
    (hconv : Convex ℝ K) (hK : IsCone K) (hne : K.Nonempty) (z : E) (z' : F) :
    (⨅ w ∈ -(polarCone B K),
      convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w) ≠ ⊥ := by
  obtain ⟨x₀, hx₀⟩ := hne
  intro hc
  have hex := isExactSum_comp_add_sub_pairing_indicatorFn (B := B) hcof hdom hconv ⟨x₀, hx₀⟩ z z'
  have hP := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex hK ⟨x₀, hx₀⟩
  rw [hc, EReal.neg_bot] at hP
  obtain ⟨r, hr⟩ := exists_comp_add_sub_pairing_eq_coe hcof.proper hdom B z z' x₀
  have hle : (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
      ≤ h (z + x₀) - ((B x₀ z' : ℝ) : EReal) := iInf₂_le x₀ hx₀
  rw [hP, hr] at hle
  exact EReal.coe_ne_top r (top_le_iff.1 hle)

/-- **Cone duality.** Let $E$ and $F$ be finite-dimensional real normed spaces with a pairing that
is compatible with both topologies. Let $h : E \to [-\infty, +\infty]$ be co-finite and finite
everywhere, let $K \subseteq E$ be a nonempty convex cone, and let $K^* = -K^\circ$. Then for
every $z \in E$ and $z^* \in F$,
$$\inf_{x \in K} \bigl\{ h(z + x) - \langle x, z^* \rangle \bigr\} + \inf_{w \in K^*} \bigl\{
  h^*(z^* + w) - \langle z, w \rangle \bigr\} = \langle z, z^* \rangle.$$

This is Corollary 31.4.3 of [rockafellar1970convex]. The identity does not need the closedness
of $K$. Co-finiteness is `ConvexAnalysis.Cofinite h`, and the condition that $h$ is finite
everywhere is `ConvexAnalysis.convexDom h = Set.univ`. -/
theorem iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing (hcof : Cofinite h)
    (hdom : convexDom h = univ)
    (hconv : Convex ℝ K) (hK : IsCone K) (hne : K.Nonempty) (z : E) (z' : F) :
    (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
        + (⨅ w ∈ -(polarCone B K), (convexConj B h (z' + w) - ((B z w : ℝ) : EReal)))
      = ((B z z' : ℝ) : EReal) := by
  have hex := isExactSum_comp_add_sub_pairing_indicatorFn (B := B) hcof hdom hconv hne z z'
  have hzero : (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
      + (⨅ w ∈ -(polarCone B K),
          convexConj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w) = 0 :=
    iInf_mem_add_iInf_mem_neg_polarCone_eq_zero hex hK hne
      (iInf_mem_neg_polarCone_convexConj_ne_bot hcof hdom hconv hK hne z z')
      (iInf_mem_neg_polarCone_convexConj_ne_top hcof z z')
  rw [iInf_mem_neg_polarCone_convexConj_eq, ← add_assoc] at hzero
  have hback : (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
        + (⨅ w ∈ -(polarCone B K), (convexConj B h (z' + w) - ((B z w : ℝ) : EReal)))
      = ((⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
          + (⨅ w ∈ -(polarCone B K), (convexConj B h (z' + w) - ((B z w : ℝ) : EReal)))
          + ((-(B z z') : ℝ) : EReal)) + ((B z z' : ℝ) : EReal) := by
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.sub_add_cancel]
  rw [hback, hzero, zero_add]

omit [FiniteDimensional ℝ F] [IsCompatiblePairing B.flip] in
/-- **The dual infimum is attained.** Let $E$ be a finite-dimensional real normed space with a
compatible pairing, let $h$ be co-finite and finite everywhere, and let $K$ be a nonempty convex
cone. Then for all $z \in E$ and $z^* \in F$ there is $w \in K^* = -K^\circ$ with
$$h^*(z^* + w) - \langle z, w \rangle = \inf_{v \in K^*} \bigl\{ h^*(z^* + v) - \langle z, v
  \rangle \bigr\}.$$

The proof uses that $h$ is finite everywhere, and not that $h$ is co-finite. -/
theorem exists_iInf_mem_neg_polarCone_eq_of_cofinite (hcof : Cofinite h) (hdom : convexDom h = univ)
    (hconv : Convex ℝ K) (hK : IsCone K) (hne : K.Nonempty) (z : E) (z' : F) :
    ∃ w ∈ -(polarCone B K), convexConj B h (z' + w) - ((B z w : ℝ) : EReal)
      = ⨅ v ∈ -(polarCone B K), (convexConj B h (z' + v) - ((B z v : ℝ) : EReal)) := by
  have hex := isExactSum_comp_add_sub_pairing_indicatorFn (B := B) hcof hdom hconv hne z z'
  obtain ⟨w, hw, hval⟩ := exists_mem_neg_polarCone_convexConj_eq_iInf hex hK hne
  rw [convexConj_comp_add_sub_pairing_eq_add_coe, iInf_mem_neg_polarCone_convexConj_eq] at hval
  exact ⟨w, hw, EReal.add_coe_right_cancel hval⟩

/-- **The dual infimum is finite.** Under the hypotheses of
`ConvexAnalysis.iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing`, the infimum $\inf_{w \in K^*}
\{h^*(z^* + w) - \langle z, w \rangle\}$ is a real number.

The infimum is attained, and the objective is finite. -/
theorem exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite (hcof : Cofinite h)
    (hdom : convexDom h = univ) (hconv : Convex ℝ K) (hK : IsCone K)
    (hne : K.Nonempty) (z : E) (z' : F) :
    ∃ r : ℝ, (⨅ w ∈ -(polarCone B K), (convexConj B h (z' + w) - ((B z w : ℝ) : EReal)))
      = (r : EReal) := by
  obtain ⟨w, -, hval⟩ :=
    exists_iInf_mem_neg_polarCone_eq_of_cofinite (B := B) hcof hdom hconv hK hne z z'
  obtain ⟨r, hr⟩ := exists_convexConj_comp_add_sub_pairing_eq_coe (B := B) hcof z z' w
  exact ⟨r, by rw [← hval, hr]⟩

/-- **The primal infimum is finite.** Under the hypotheses of
`ConvexAnalysis.iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing`, the infimum $\inf_{x \in K}
\{h(z + x) - \langle x, z^* \rangle\}$ is a real number.

By the duality identity it is $\langle z, z^* \rangle$ minus the dual infimum, which is finite. -/
theorem exists_iInf_mem_eq_coe_of_cofinite (hcof : Cofinite h) (hdom : convexDom h = univ)
    (hconv : Convex ℝ K) (hK : IsCone K) (hne : K.Nonempty) (z : E) (z' : F) :
    ∃ s : ℝ, (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal))) = (s : EReal) := by
  obtain ⟨r, hr⟩ :=
    exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite (B := B) hcof hdom hconv hK hne z z'
  have hex := isExactSum_comp_add_sub_pairing_indicatorFn (B := B) hcof hdom hconv hne z z'
  have hP := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex hK hne
  rw [iInf_mem_neg_polarCone_convexConj_eq, hr, ← EReal.coe_add] at hP
  exact ⟨-(r + -(B z z')), by rw [hP, ← EReal.coe_neg]⟩

/-- **The primal infimum is attained.** Under the hypotheses of
`ConvexAnalysis.iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing`, and if moreover $K$ is closed,
there is $x \in K$ with
$$h(z + x) - \langle x, z^* \rangle = \inf_{u \in K} \bigl\{ h(z + u) - \langle u, z^* \rangle
  \bigr\}.$$

The proof of this result uses the co-finiteness of $h$ and the closedness of $K$. -/
theorem exists_iInf_mem_eq_of_cofinite (hcof : Cofinite h) (hdom : convexDom h = univ)
    (hconv : Convex ℝ K) (hK : IsCone K) (hne : K.Nonempty) (hcl : IsClosed K)
    (z : E) (z' : F) :
    ∃ x ∈ K, h (z + x) - ((B x z' : ℝ) : EReal)
      = ⨅ u ∈ K, (h (z + u) - ((B u z' : ℝ) : EReal)) := by
  have hconvf := convexFn_comp_add_sub_pairing hcof.convex B z z'
  have hpf := properConvex_comp_add_sub_pairing hcof.proper hdom B z z'
  have hdomf := convexDom_comp_add_sub_pairing_eq_univ hcof.proper hdom B z z'
  have hclf : ClosedConvex (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) :=
    (closedConvex_iff_lowerSemicontinuous hpf.ne_bot).2
      (hconvf.continuous_of_convexDom_eq_univ hpf hdomf).lowerSemicontinuous
  exact exists_mem_eq_iInf_of_isExactSum_convexConj (convexBiconj_eq_self hconvf hclf)
    (isExactSum_convexConj_comp_add_sub_pairing_indicatorFn hcof hdom z z') hconv hK hne hcl

end DualityIdentity

end ConvexAnalysis
