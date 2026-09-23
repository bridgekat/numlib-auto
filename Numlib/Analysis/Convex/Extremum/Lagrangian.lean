import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Extremum.Perturbation

/-!
# Lagrangians of generalized convex programs

The **Lagrangian** of the program associated with a bifunction `F` is
`L(v, x) = ⨅ u (⟨u, v⟩ + F u x)`, the partial *concave* conjugate of `F` in the perturbation
variable. Identifying it as such is the design of this file: concavity of `L(·, x)`, its closedness
and the biconjugation `L** = cl L` are concave-conjugate lemmas applied pointwise in `x`. The one
step with content is the exchange `⨅ x L(v, x) = ⨅ u (⟨u, v⟩ + inf F u)`, which turns the
definition of a Kuhn–Tucker vector into a statement about `L`.

## Main definitions

* `lagrangian B F` — the Lagrangian `L` of the program associated with `F`.

## Main results

* `lagrangian_eq_concaveConj` — `L(·, x)` is the concave conjugate of `-F(·)(x)`.
* `iInf_lagrangian` — `⨅ x L(v, x) = ⨅ u (⟨u, v⟩ + inf F u)`; its mirror `iSup_lagrangian` —
  `⨆ v L(v, x) = (cl F(·)(x))(0)`, from `convexCl_zero_eq_iSup_iInf`, Fenchel–Moreau at the origin.
* `mem_kuhnTucker_iff_iInf_lagrangian` — `v` is a Kuhn–Tucker vector exactly when `⨅ x L(v, x)` is
  finite and equal to the optimal value.

## References

* [rockafellar1970convex] §29.
-/

namespace ConvexAnalysis

section Defs

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V} {x : X}

/-- The **Lagrangian** of the generalized convex program associated with `F`:
`L(v, x) = ⨅ u (⟨u, v⟩ + F u x)`. -/
noncomputable def lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V → X → EReal :=
  fun v x => ⨅ u, ((B u v : ℝ) : EReal) + F u x

theorem lagrangian_apply (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x = ⨅ u, ((B u v : ℝ) : EReal) + F u x := rfl

/-- For each fixed `x`, `L(·, x)` is the concave conjugate of `u ↦ -(F u x)`. -/
theorem lagrangian_eq_concaveConj (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x = concaveConj B (fun u => -(F u x)) v := by
  rw [lagrangian_apply, concaveConj_apply]
  exact iInf_congr fun u => by rw [sub_eq_add_neg, neg_neg]

/-- The Lagrangian is never above the objective it comes from, taken at `u = 0`. -/
theorem lagrangian_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x ≤ F 0 x := by
  refine le_trans (iInf_le _ 0) (le_of_eq ?_)
  rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_add]

/-- Minimising the Lagrangian over `x` is the same as pricing the perturbations:
`⨅ x L(v, x) = ⨅ u (⟨u, v⟩ + inf F u)`. -/
theorem iInf_lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ x, lagrangian B F v x) = ⨅ u, (((B u v : ℝ) : EReal) + infBifun F u) := by
  rw [show (⨅ x, lagrangian B F v x) = ⨅ x, ⨅ u, (((B u v : ℝ) : EReal) + F u x) from rfl,
    iInf_comm]
  refine iInf_congr fun u => ?_
  rw [infBifun_apply, add_comm, EReal.iInf_add_coe]
  exact iInf_congr fun x => add_comm _ _

/-- The Lagrangian description of Kuhn–Tucker vectors: `v` is one exactly when `⨅ x L(v, x)` is
finite and equal to the optimal value. -/
theorem mem_kuhnTucker_iff_iInf_lagrangian :
    v ∈ KuhnTucker B F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      (⨅ x, lagrangian B F v x) = infBifun F 0 := by
  rw [KuhnTucker, Set.mem_ofPred_eq, iInf_lagrangian]

/-- Weak duality: `⨅ x L(v, x)` is never above the optimal value, whatever the price `v`. -/
theorem iInf_lagrangian_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ x, lagrangian B F v x) ≤ infBifun F 0 := by
  rw [iInf_lagrangian]
  exact iInf_add_infBifun_le B F v

end Defs

/-! ### The closure of a convex function at the origin -/

section ClosureAtZero

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- `EReal.neg_coe_sub` with the difference read as a sum. -/
private theorem neg_coe_sub_eq {c : ℝ} {w : EReal} :
    -(((c : ℝ) : EReal) - w) = w + ((-c : ℝ) : EReal) := by
  rw [EReal.neg_coe_sub]
  rfl

/-- **Fenchel–Moreau at the origin.** For a convex `f`, the closure at `0` is the supremum over the
dual variable of the infimum of `x ↦ ⟨x, y⟩ + f x`. Everything below rests on this computation. -/
theorem convexCl_zero_eq_iSup_iInf (hf : ConvexFn f) :
    convexCl f 0 = ⨆ y : F, ⨅ x : E, (((B x y : ℝ) : EReal) + f x) := by
  have hsurj : Function.Surjective (fun y : F => -y) := fun y => ⟨-y, neg_neg y⟩
  have hterm : ∀ y : F, ((B (0 : E) y : ℝ) : EReal) - convexConj B f y
      = ⨅ x : E, (((B x (-y) : ℝ) : EReal) + f x) := by
    intro y
    rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_sub, convexConj_apply,
      EReal.neg_iSup]
    refine iInf_congr fun x => ?_
    have hb : (B x (-y) : ℝ) = -(B x y) := by rw [map_neg]
    rw [neg_coe_sub_eq, hb, add_comm]
  rw [← convexBiconj_eq_convexCl (B := B) hf, convexBiconj_apply, iSup_congr hterm]
  exact hsurj.iSup_comp fun y : F => ⨅ x : E, (((B x y : ℝ) : EReal) + f x)

end ClosureAtZero

section LagrangianSup

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {x : X}

/-- The mirror of `iInf_lagrangian`: *maximising* the Lagrangian over the price variable gives
the closure of the objective slice at the origin. This is Fenchel–Moreau at the origin, read at
`u ↦ F u x`. -/
theorem iSup_lagrangian (hf : ConvexFn fun u => F u x) :
    (⨆ w, lagrangian Bu F w x) = convexCl (fun u => F u x) 0 :=
  (convexCl_zero_eq_iSup_iInf (B := Bu) hf).symm

end LagrangianSup


section Concave

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {x : X}

/-- The Lagrangian is concave in the price variable, with no hypothesis on `F`. -/
theorem concaveFn_lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (x : X) :
    ConcaveFn (fun v => lagrangian B F v x) := by
  have h : (fun v => lagrangian B F v x) = concaveConj B (fun u => -(F u x)) :=
    funext fun v => lagrangian_eq_concaveConj B F v x
  rw [h]
  exact concaveFn_concaveConj B _

end Concave

end ConvexAnalysis
