import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Optimization.Fenchel

/-!
# Duality between a co-finite function and a closed convex cone

Let `h` be convex, finite everywhere and *co-finite*, let `K` be a nonempty closed convex cone and
let `K* = -K°`. Then for every `z` and `z*`

```
inf_{x ∈ K} {h (z + x) - ⟨z*, x⟩} + inf_{x* ∈ K*} {h* (z* + x*) - ⟨z, x*⟩} = ⟨z, z*⟩,
```

with both infima finite and attained: a duality between `h` and `h*` parametrised by a point of
each space.

The proof runs through the auxiliary function `f = h (z + ·) - ⟨·, z*⟩`, whose conjugate is the
dual objective shifted down by the constant `⟨z, z*⟩`. Finiteness of `h` gives `dom f = E` and
co-finiteness of `h` gives `dom f* = F`; those are the two constraint qualifications for duality
between a convex function and a cone, each in its strongest form.

## Main results

* `iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing` — the identity (Corollary 31.4.3 in [^1]).
* `exists_iInf_mem_eq_of_cofinite`, `exists_iInf_mem_neg_polarCone_eq_of_cofinite` — both infima
  are attained.
* `exists_iInf_mem_eq_coe_of_cofinite`, `exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite` — both
  infima are finite.

## Implementation notes

Closedness of `K` is used only for attainment of the *primal* infimum, whose proof runs through the
bipolar `K** = K`; the identity, finiteness of both infima and attainment of the dual infimum need
only that `K` is a nonempty convex cone. Finite-dimensionality enters only through continuity of a
convex function that is finite everywhere, and the everywhere-finite conjugate of a co-finite one.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §§12, 13, 31.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### The translated, tilted function -/

section Shift

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {h : E → EReal}

/-- `f = h (z + ·) - ⟨·, z*⟩` rewritten as `h (z + ·)` plus a real-valued linear term. -/
theorem comp_add_sub_pairing_eq_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (z : E) (z' : F) :
    (fun x => h (z + x) - ((B x z' : ℝ) : EReal))
      = fun x => h (z + x) + ((-(B x z') : ℝ) : EReal) := by
  funext x
  rw [_root_.EReal.coe_neg, ← sub_eq_add_neg]

/-- `f` is convex: a translate of `h` plus a linear term. -/
theorem convexFn_comp_add_sub_pairing (hh : ConvexFn h) (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : E) (z' : F) :
    ConvexFn (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) := by
  rw [comp_add_sub_pairing_eq_add_coe]
  refine convexFn_add_coe (hh.comp_add_left z) fun x y a b _ => ?_
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- When `h` is finite everywhere so is `f`: the tilt is real. -/
theorem exists_comp_add_sub_pairing_eq_coe (hp : Proper h) (hdom : dom h = univ)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : E) (z' : F) (x : E) :
    ∃ r : ℝ, h (z + x) - ((B x z' : ℝ) : EReal) = (r : EReal) := by
  obtain ⟨p, hp'⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot (z + x))
    (by rw [← mem_dom, hdom]; trivial)
  exact ⟨p - B x z', by rw [hp', ← _root_.EReal.coe_sub]⟩

/-- `f` is proper whenever `h` is finite everywhere. -/
theorem proper_comp_add_sub_pairing (hp : Proper h) (hdom : dom h = univ)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : E) (z' : F) :
    Proper (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) := by
  refine ⟨⟨0, ?_⟩, fun x => ?_⟩
  · obtain ⟨r, hr⟩ := exists_comp_add_sub_pairing_eq_coe hp hdom B z z' 0
    rw [mem_dom, hr]
    exact _root_.EReal.coe_lt_top r
  · obtain ⟨r, hr⟩ := exists_comp_add_sub_pairing_eq_coe hp hdom B z z' x
    rw [hr]
    exact _root_.EReal.coe_ne_bot r

/-- `f` is finite everywhere whenever `h` is. -/
theorem dom_comp_add_sub_pairing_eq_univ (hp : Proper h) (hdom : dom h = univ)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : E) (z' : F) :
    dom (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨r, hr⟩ := exists_comp_add_sub_pairing_eq_coe hp hdom B z z' x
  rw [mem_dom, hr]
  exact _root_.EReal.coe_lt_top r

/-- `f*` is the dual objective shifted down by the constant `⟨z, z*⟩`, with the two subtractions
collected into a single real summand. -/
theorem conj_comp_add_sub_pairing_eq_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (z : E)
    (z' : F) (w : F) :
    conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w
      = (conj B h (z' + w) - ((B z w : ℝ) : EReal)) + ((-(B z z') : ℝ) : EReal) := by
  rw [conj_comp_add_sub_pairing, _root_.EReal.coe_neg, ← sub_eq_add_neg]

/-- The infimum of `f*` over `K*` is the dual infimum for `h` shifted down by `⟨z, z*⟩`; the shift
is a real constant, so it slides out of the infimum. -/
theorem iInf_mem_neg_polarCone_conj_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (K : Set E)
    (z : E) (z' : F) :
    (⨅ w ∈ -(polarCone B K), conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w)
      = (⨅ w ∈ -(polarCone B K), (conj B h (z' + w) - ((B z w : ℝ) : EReal)))
        + ((-(B z z') : ℝ) : EReal) := by
  rw [EReal.biInf_add_coe]
  exact iInf_congr fun w => iInf_congr fun _ => conj_comp_add_sub_pairing_eq_add_coe B h z z' w

end Shift

/-! ### The cone duality identity -/

section DualityIdentity

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
  {h : E → EReal} {K : Set E}

omit [FiniteDimensional ℝ E] in
/-- A co-finite `h` has an everywhere-finite conjugate. -/
theorem dom_conj_eq_univ_of_cofinite (hcof : Cofinite h) : dom (conj B h) = univ :=
  (cofinite_iff_dom_conj_eq_univ (B := B) hcof.toClosedProperConvexFn).1 hcof

omit [FiniteDimensional ℝ E] in
/-- The dual objective is finite at every point: `h*` is finite everywhere, and the tilt is real. -/
theorem exists_conj_comp_add_sub_pairing_eq_coe (hcof : Cofinite h) (z : E) (z' : F) (w : F) :
    ∃ r : ℝ, conj B h (z' + w) - ((B z w : ℝ) : EReal) = (r : EReal) := by
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (conj_ne_bot hcof.proper.dom_nonempty (z' + w))
    (by rw [← mem_dom, dom_conj_eq_univ_of_cofinite (B := B) hcof]; trivial)
  exact ⟨s - B z w, by rw [hs, ← _root_.EReal.coe_sub]⟩

omit [FiniteDimensional ℝ E] in
/-- `f*` is finite everywhere, because the conjugate of a co-finite function is. -/
theorem dom_conj_comp_add_sub_pairing_eq_univ (hcof : Cofinite h) (z : E) (z' : F) :
    dom (conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal))) = univ := by
  refine eq_univ_of_forall fun w => ?_
  obtain ⟨r, hr⟩ := exists_conj_comp_add_sub_pairing_eq_coe (B := B) hcof z z' w
  rw [mem_dom, conj_comp_add_sub_pairing_eq_add_coe, hr, ← _root_.EReal.coe_add]
  exact _root_.EReal.coe_lt_top _

omit [FiniteDimensional ℝ F] [IsCompatiblePairing B.flip] in
/-- `f` is finite everywhere, hence continuous, so it adds exactly to `δ(·|K)`: the constraint
qualification on the primal side. -/
theorem isExactSum_comp_add_sub_pairing_indicatorFn (hcof : Cofinite h) (hdom : dom h = univ)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (z : E) (z' : F) :
    IsExactSum B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) (indicatorFn K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hconvf := convexFn_comp_add_sub_pairing hcof.convex B z z'
  have hpf := proper_comp_add_sub_pairing hcof.proper hdom B z z'
  have hdomf := dom_comp_add_sub_pairing_eq_univ hcof.proper hdom B z z'
  refine IsExactSum.of_continuousAt hconvf hpf (convexFn_indicatorFn.2 hconv)
    ⟨⟨x₀, by rw [dom_indicatorFn]; exact hx₀⟩, indicatorFn_ne_bot K⟩
    (by rw [hdomf]; trivial) (by rw [dom_indicatorFn]; exact hx₀) ?_
  exact (hconvf.continuous_of_dom_eq_univ hpf hdomf).continuousAt

omit [FiniteDimensional ℝ E] in
/-- `f*` is finite everywhere too, so it adds exactly to `δ(·|K*)`: the constraint qualification on
the dual side, which is what co-finiteness of `h` supplies. -/
theorem isExactSum_conj_comp_add_sub_pairing_indicatorFn (hcof : Cofinite h) (hdom : dom h = univ)
    (z : E) (z' : F) :
    IsExactSum B.flip (conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)))
      (indicatorFn (-(polarCone B K))) := by
  have hpf : Proper (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) :=
    proper_comp_add_sub_pairing hcof.proper hdom B z z'
  have hdomc := dom_conj_comp_add_sub_pairing_eq_univ (B := B) hcof z z'
  have hpc : Proper (conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal))) :=
    ⟨⟨0, by rw [hdomc]; trivial⟩, fun w => conj_ne_bot hpf.dom_nonempty w⟩
  refine IsExactSum.of_continuousAt (convexFn_conj B _) hpc
    (convexFn_indicatorFn.2 (convex_neg_polarCone B K))
    ⟨⟨0, by rw [dom_indicatorFn]; exact zero_mem_neg_polarCone B K⟩, indicatorFn_ne_bot _⟩
    (by rw [hdomc]; trivial)
    (by rw [dom_indicatorFn]; exact zero_mem_neg_polarCone B K) ?_
  exact ((convexFn_conj B _).continuous_of_dom_eq_univ hpc hdomc).continuousAt

omit [FiniteDimensional ℝ E] in
/-- The dual infimum is not `⊤`: the origin lies in `K*`, where the value is finite. -/
theorem iInf_mem_neg_polarCone_conj_ne_top (hcof : Cofinite h) (z : E) (z' : F) :
    (⨅ w ∈ -(polarCone B K),
      conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w) ≠ ⊤ := by
  have hdomc := dom_conj_comp_add_sub_pairing_eq_univ (B := B) hcof z z'
  have hlt : conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) 0 < ⊤ := by
    rw [← mem_dom, hdomc]; trivial
  have hge : (⨅ w ∈ -(polarCone B K),
        conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w)
      ≤ conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) 0 :=
    iInf₂_le (0 : F) (zero_mem_neg_polarCone B K)
  exact (lt_of_le_of_lt hge hlt).ne

omit [FiniteDimensional ℝ F] [IsCompatiblePairing B.flip] in
/-- The dual infimum is not `⊥`: its negative is the primal infimum, which is bounded above by a
finite value. -/
theorem iInf_mem_neg_polarCone_conj_ne_bot (hcof : Cofinite h) (hdom : dom h = univ)
    (hconv : Convex ℝ K) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z : E) (z' : F) :
    (⨅ w ∈ -(polarCone B K),
      conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w) ≠ ⊥ := by
  obtain ⟨x₀, hx₀⟩ := hne
  intro hc
  have hex := isExactSum_comp_add_sub_pairing_indicatorFn (B := B) hcof hdom hconv ⟨x₀, hx₀⟩ z z'
  have hP := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex hK ⟨x₀, hx₀⟩
  rw [hc, _root_.EReal.neg_bot] at hP
  obtain ⟨r, hr⟩ := exists_comp_add_sub_pairing_eq_coe hcof.proper hdom B z z' x₀
  have hle : (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
      ≤ h (z + x₀) - ((B x₀ z' : ℝ) : EReal) := iInf₂_le x₀ hx₀
  rw [hP, hr] at hle
  exact _root_.EReal.coe_ne_top r (top_le_iff.1 hle)

/-- **Cone duality.** For `h` convex, finite everywhere and co-finite and `K` a nonempty convex
cone, the primal infimum over `K` and the dual infimum over `K* = -K°` add to `⟨z, z*⟩`. Closedness
of `K` is not needed for the identity. -/
theorem iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing (hcof : Cofinite h) (hdom : dom h = univ)
    (hconv : Convex ℝ K) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z : E) (z' : F) :
    (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
        + (⨅ w ∈ -(polarCone B K), (conj B h (z' + w) - ((B z w : ℝ) : EReal)))
      = ((B z z' : ℝ) : EReal) := by
  have hex := isExactSum_comp_add_sub_pairing_indicatorFn (B := B) hcof hdom hconv hne z z'
  have hzero : (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
      + (⨅ w ∈ -(polarCone B K),
          conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) w) = 0 :=
    iInf_mem_add_iInf_mem_neg_polarCone_eq_zero hex hK hne
      (iInf_mem_neg_polarCone_conj_ne_bot hcof hdom hconv hK hne z z')
      (iInf_mem_neg_polarCone_conj_ne_top hcof z z')
  rw [iInf_mem_neg_polarCone_conj_eq, ← add_assoc] at hzero
  have hback : (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
        + (⨅ w ∈ -(polarCone B K), (conj B h (z' + w) - ((B z w : ℝ) : EReal)))
      = ((⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal)))
          + (⨅ w ∈ -(polarCone B K), (conj B h (z' + w) - ((B z w : ℝ) : EReal)))
          + ((-(B z z') : ℝ) : EReal)) + ((B z z' : ℝ) : EReal) := by
    rw [_root_.EReal.coe_neg, ← sub_eq_add_neg, _root_.EReal.sub_add_cancel]
  rw [hback, hzero, zero_add]

omit [FiniteDimensional ℝ F] [IsCompatiblePairing B.flip] in
/-- The dual infimum is attained. Only finiteness of `h` is used here, not co-finiteness. -/
theorem exists_iInf_mem_neg_polarCone_eq_of_cofinite (hcof : Cofinite h) (hdom : dom h = univ)
    (hconv : Convex ℝ K) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z : E) (z' : F) :
    ∃ w ∈ -(polarCone B K), conj B h (z' + w) - ((B z w : ℝ) : EReal)
      = ⨅ v ∈ -(polarCone B K), (conj B h (z' + v) - ((B z v : ℝ) : EReal)) := by
  have hex := isExactSum_comp_add_sub_pairing_indicatorFn (B := B) hcof hdom hconv hne z z'
  obtain ⟨w, hw, hval⟩ := exists_mem_neg_polarCone_conj_eq_iInf hex hK hne
  rw [conj_comp_add_sub_pairing_eq_add_coe, iInf_mem_neg_polarCone_conj_eq] at hval
  exact ⟨w, hw, EReal.add_coe_right_cancel hval⟩

/-- The dual infimum is finite, being attained where the objective is. -/
theorem exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite (hcof : Cofinite h)
    (hdom : dom h = univ) (hconv : Convex ℝ K) (hK : ∀ a : ℝ, 0 < a → a • K = K)
    (hne : K.Nonempty) (z : E) (z' : F) :
    ∃ r : ℝ, (⨅ w ∈ -(polarCone B K), (conj B h (z' + w) - ((B z w : ℝ) : EReal)))
      = (r : EReal) := by
  obtain ⟨w, -, hval⟩ :=
    exists_iInf_mem_neg_polarCone_eq_of_cofinite (B := B) hcof hdom hconv hK hne z z'
  obtain ⟨r, hr⟩ := exists_conj_comp_add_sub_pairing_eq_coe (B := B) hcof z z' w
  exact ⟨r, by rw [← hval, hr]⟩

/-- The primal infimum is finite, being the negative of the dual infimum up to the constant
`⟨z, z*⟩`. -/
theorem exists_iInf_mem_eq_coe_of_cofinite (hcof : Cofinite h) (hdom : dom h = univ)
    (hconv : Convex ℝ K) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z : E) (z' : F) :
    ∃ s : ℝ, (⨅ x ∈ K, (h (z + x) - ((B x z' : ℝ) : EReal))) = (s : EReal) := by
  obtain ⟨r, hr⟩ :=
    exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite (B := B) hcof hdom hconv hK hne z z'
  have hex := isExactSum_comp_add_sub_pairing_indicatorFn (B := B) hcof hdom hconv hne z z'
  have hP := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex hK hne
  rw [iInf_mem_neg_polarCone_conj_eq, hr, ← _root_.EReal.coe_add] at hP
  exact ⟨-(r + -(B z z')), by rw [hP, ← _root_.EReal.coe_neg]⟩

/-- The primal infimum is attained; this is where co-finiteness of `h` and closedness of `K` are
used. -/
theorem exists_iInf_mem_eq_of_cofinite (hcof : Cofinite h) (hdom : dom h = univ)
    (hconv : Convex ℝ K) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K)
    (z : E) (z' : F) :
    ∃ x ∈ K, h (z + x) - ((B x z' : ℝ) : EReal)
      = ⨅ u ∈ K, (h (z + u) - ((B u z' : ℝ) : EReal)) := by
  have hconvf := convexFn_comp_add_sub_pairing hcof.convex B z z'
  have hpf := proper_comp_add_sub_pairing hcof.proper hdom B z z'
  have hdomf := dom_comp_add_sub_pairing_eq_univ hcof.proper hdom B z z'
  have hclf : ClosedFn (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) :=
    (closedFn_iff_lowerSemicontinuous hpf.ne_bot).2
      (hconvf.continuous_of_dom_eq_univ hpf hdomf).lowerSemicontinuous
  exact exists_mem_eq_iInf_of_isExactSum_conj (biconj_eq_self hconvf hclf)
    (isExactSum_conj_comp_add_sub_pairing_indicatorFn hcof hdom z z') hconv hK hne hcl

end DualityIdentity

end ConvexAnalysis
