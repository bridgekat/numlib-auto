import Numlib.Analysis.Convex.Bifunction.LinearProcess
import Numlib.Analysis.Convex.Optimization.Adjoint
import Numlib.Analysis.Convex.Optimization.Perturbation
import Numlib.Analysis.Convex.Saddle.Minimax
import NumlibSurface.Rockafellar.Chapter05.Section25

/-!
# Rockafellar §29: bifunctions and generalized convex programs

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §29
(pp. 291–306): the generalization of an ordinary convex program to a *convex bifunction* — an
objective function together with a distinguished family of perturbations of it — and the
identification of its Kuhn–Tucker vectors with the subgradients of the perturbation function at
the origin. This is the hinge of Part VI: §30's duality theory is stated entirely in this
vocabulary.

All 12 numbered results of §29 are formalized: Theorems 29.1, 29.2, 29.3 and 29.4 and Corollaries
29.1.1–29.1.6, 29.3.1 and 29.4.1. Corollary 29.4.1 is printed with no proof.

Almost all of §29's vocabulary is the backbone's under the book's own names: `Bifun (Rn m) (Rn n)`,
`graphFn`, `ConvexBifun`, `ClosedBifun`, `domBifun`, `infBifun` for the perturbation function
`inf F`, `KuhnTucker (pairing m) F`, `lagrangian (pairing m) F`, `Consistent`,
`StronglyConsistent`, `StrictlyConsistent`, `PolyhedralBifun`, and `clBifun` for `cl F`. The
objective function `F0` is `F 0`; the optimal value in `(P)` is `infBifun F 0`. `IsOptimalSolution`
is deliberately *not* `argmin (F 0)` — the book asks for `(F0)(x)` to be *finite* and equal to the
optimal value, so an inconsistent program has no optimal solutions although `argmin (F 0) = ℝⁿ`.

## Main results

* `theorem_29_1`, `theorem_29_1_convexFn`, `theorem_29_1_dom`, `theorem_29_1_set` — the
  perturbation function `inf F` is convex with `dom (inf F) = dom F`, and at a finite optimal value
  the Kuhn–Tucker vectors are exactly `-∂(inf F)(0)`.
* `corollary_29_1_1_*` — the ε-subgradient description, the directional derivative
  `(inf F)'(0; ·)`, and convexity, closedness and the support function of the Kuhn–Tucker set.
* `corollary_29_1_2`, `corollary_29_1_3`, `corollary_29_1_3_eq`, `corollary_29_1_3_partial` —
  when no Kuhn–Tucker vector exists, and when there is exactly one, namely `-∇(inf F)(0)`.
* `corollary_29_1_4_nonempty`, `corollary_29_1_4_dirDeriv`, `corollary_29_1_5_isCompact` with its
  five clauses, `corollary_29_1_6_bot`, `corollary_29_1_6_top` — strong and strict consistency, and
  the dichotomy `inf Fu = -∞` for one `u` or for none.
* `theorem_29_2_objective`, `theorem_29_2_infBifun`, `theorem_29_2_argmin_nonempty`,
  `theorem_29_2_kuhnTucker_nonempty`, `theorem_29_2_polyhedral_argmin`,
  `theorem_29_2_polyhedral_kuhnTucker` — the polyhedral case, where consistency alone suffices.
* `theorem_29_3`, `theorem_29_3_isSaddlePoint`, `corollary_29_3_1_stronglyConsistent`,
  `corollary_29_3_1_strictlyConsistent`, `corollary_29_3_1_polyhedral` — optimality plus a
  Kuhn–Tucker vector is a saddle-point of the Lagrangian, under three constraint qualifications.
* `theorem_29_4_apply`, `theorem_29_4_inf`, `theorem_29_4_dom_subset`,
  `theorem_29_4_dom_subset_closure`, and the `corollary_29_4_1_*` clauses — what closing a
  bifunction preserves.

## Where the book needs correcting

**Corollary 29.4.1 is false as printed.** Its perturbation clause — that the perturbation functions
of `(P)` and `(cl P)` agree on a neighbourhood of `0` — drops the properness that its own
Theorem 29.4 carries. `corollary_29_4_1_perturbation` transcribes the claim as printed and
`corollary_29_4_1_perturbation_false` refutes it, with the counterexample `originBifun` on `ℝ¹`.
The corrected statement is `corollary_29_4_1_eventually`, which adds `Proper (graphFn F)`. Every
other clause of the corollary holds as printed and is proved here.
-/

open Filter Topology
open scoped Pointwise

namespace Rockafellar

open ConvexAnalysis

/-! ### The section's vocabulary -/

section Vocabulary

variable {m n : ℕ}

/-- The **graph domain** of a bifunction: the effective domain of its graph function, a convex
subset of `ℝᵐ × ℝⁿ`. -/
def graphDomain (F : Bifun (Rn m) (Rn n)) : Set (Rn m × Rn n) := dom (graphFn F)

theorem graphDomain_eq (F : Bifun (Rn m) (Rn n)) : graphDomain F = dom (graphFn F) := rfl

@[simp] theorem mem_graphDomain {F : Bifun (Rn m) (Rn n)} {u : Rn m} {x : Rn n} :
    (u, x) ∈ graphDomain F ↔ F u x < ⊤ := Iff.rfl

/-- **`dom F` is the projection of the graph domain on `ℝᵐ`**, and is therefore a convex set. This
is the identification every relative-interior step of Theorem 29.4 runs on. -/
theorem domBifun_eq_image_graphDomain (F : Bifun (Rn m) (Rn n)) :
    domBifun F = LinearMap.fst ℝ (Rn m) (Rn n) '' graphDomain F :=
  domBifun_eq_image_dom_graphFn F

/-- The graph domain of a convex bifunction is convex. -/
theorem convex_graphDomain {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F) :
    Convex ℝ (graphDomain F) :=
  ConvexFn.convex_dom hF

/-- An **optimal solution** to the convex program `(P)` associated with `F`: a vector `x` at which
`(F0)(x)` is *finite* and equal to the optimal value in `(P)`. Not `argmin (F 0)`: Rockafellar is
explicit that "we do not speak of optimal solutions to `(P)` when `(P)` is inconsistent", and an
optimal value of `-∞` is excluded by the same clause. -/
def IsOptimalSolution (F : Bifun (Rn m) (Rn n)) (x : Rn n) : Prop :=
  F 0 x ≠ ⊤ ∧ F 0 x ≠ ⊥ ∧ F 0 x = infBifun F 0

/-- **The bridge to the backbone's minimum set**: the optimal solutions are empty unless `F0` is
proper, and are its minimum set when it is. The second hypothesis is consistency. -/
theorem isOptimalSolution_iff_mem_argmin {F : Bifun (Rn m) (Rn n)} {x : Rn n}
    (hb : ∀ y, F 0 y ≠ ⊥) (ht : infBifun F 0 ≠ ⊤) :
    IsOptimalSolution F x ↔ x ∈ argmin (F 0) := by
  constructor
  · rintro ⟨-, -, hx⟩
    intro z
    rw [hx, infBifun_apply]
    exact iInf_le _ z
  · intro hx
    have hval : F 0 x = infBifun F 0 := by
      rw [infBifun_apply]
      exact le_antisymm (le_iInf hx) (iInf_le _ x)
    exact ⟨by rw [hval]; exact ht, hb x, hval⟩

/-- A program whose optimal value is `-∞` has no optimal solutions, whatever else is true of it: the
book's definition asks for a *finite* value. -/
theorem not_isOptimalSolution_of_infBifun_eq_bot {F : Bifun (Rn m) (Rn n)} {x : Rn n}
    (h : infBifun F 0 = ⊥) : ¬ IsOptimalSolution F x := by
  rintro ⟨-, hne, hval⟩
  exact hne (by rw [hval, h])

/-- **The saddle-point condition of Theorem 29.3 as the book writes it**:
`L(u*, x̄) ≤ L(ū*, x̄) ≤ L(ū*, x)` for every `u*` and every `x`. -/
theorem isSaddlePoint_lagrangian_iff_forall (F : Bifun (Rn m) (Rn n)) (v : Rn m) (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) ↔
      (∀ w : Rn m, lagrangian (pairing m) F w x ≤ lagrangian (pairing m) F v x) ∧
        ∀ y : Rn n, lagrangian (pairing m) F v x ≤ lagrangian (pairing m) F v y :=
  Iff.rfl

end Vocabulary

/-! ### The indicator bifunction of a linear transformation -/

section LinearIndicator

variable {m n : ℕ}

/-- The **`(+∞)` indicator bifunction of a linear transformation `A`**: `(Fu)(x) = δ(x | Au)`. It is
the backbone's indicator bifunction of the convex process `ofLinearMap A`. -/
noncomputable def linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) : Bifun (Rn m) (Rn n) :=
  (ConvexProcess.ofLinearMap A).indicatorBifun

theorem linearIndicatorBifun_apply (A : Rn m →ₗ[ℝ] Rn n) (u : Rn m) (x : Rn n) :
    linearIndicatorBifun A u x = indicatorFn {A u} x := by
  rw [linearIndicatorBifun, ConvexProcess.indicatorBifun_apply, ConvexProcess.eval_ofLinearMap]

/-- The graph function of `linearIndicatorBifun A` is the indicator of the graph of `A`, a subspace
of `ℝᵐ⁺ⁿ`. -/
theorem graphFn_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    graphFn (linearIndicatorBifun A) = indicatorFn {p : Rn m × Rn n | p.2 = A p.1} :=
  ConvexProcess.graphFn_indicatorBifun _

theorem convexBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    ConvexBifun (linearIndicatorBifun A) :=
  ConvexProcess.convexBifun_indicatorBifun _

theorem closedBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    ClosedBifun (linearIndicatorBifun A) := by
  rw [ClosedBifun, graphFn_linearIndicatorBifun]
  refine closedFn_indicatorFn ?_
  have hker : {p : Rn m × Rn n | p.2 = A p.1}
      = LinearMap.ker ((LinearMap.snd ℝ (Rn m) (Rn n)) - A ∘ₗ LinearMap.fst ℝ (Rn m) (Rn n)) := by
    ext p
    simp [LinearMap.mem_ker, sub_eq_zero]
  rw [hker]
  exact (LinearMap.ker _).closed_of_finiteDimensional

theorem proper_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    Proper (graphFn (linearIndicatorBifun A)) := by
  rw [graphFn_linearIndicatorBifun]
  exact ⟨⟨(0, A 0), by simp⟩, indicatorFn_ne_bot _⟩

@[simp] theorem domBifun_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) :
    domBifun (linearIndicatorBifun A) = Set.univ := by
  rw [linearIndicatorBifun, ConvexProcess.domBifun_indicatorBifun,
    ConvexProcess.dom_ofLinearMap]

end LinearIndicator

/-! ### Theorem 29.1 -/

section Theorem291

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {v : Rn m}

/-- **Theorem 29.1**, first assertion: the perturbation function `inf F` of a convex program is
convex. Theorem 5.7 at the projection `(u, x) ↦ u`, of which `inf F` is the image. -/
theorem theorem_29_1_convexFn (hF : ConvexBifun F) : ConvexFn (infBifun F) :=
  convexFn_infBifun hF

/-- **Theorem 29.1**, first assertion, second half: `dom (inf F) = dom F`. Needs no hypothesis on
`F`: `inf F` is `+∞` at `u` only if `Fu` is the constant `+∞`. -/
theorem theorem_29_1_dom (F : Bifun (Rn m) (Rn n)) : dom (infBifun F) = domBifun F :=
  dom_infBifun F

/-- The reformulation of the definition of a Kuhn–Tucker vector that the book records immediately
after giving it: `inf F0` is finite and `inf Fu + ⟨u*, u⟩ ≥ inf F0` for every `u`. -/
theorem theorem_29_1_forall_le :
    v ∈ KuhnTucker (pairing m) F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      ∀ u : Rn m, infBifun F 0 ≤ ((pairing m u v : ℝ) : EReal) + infBifun F u :=
  mem_kuhnTucker_iff_forall_le

/-- **Theorem 29.1**, second assertion: at a finite optimal value the Kuhn–Tucker vectors for `(P)`
are precisely the `u*` with `-u* ∈ ∂(inf F)(0)`. **No convexity is used**, although the book states
the whole theorem for a convex bifunction: this assertion rearranges the definition. -/
theorem theorem_29_1 (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker (pairing m) F ↔ -v ∈ subdifferential (pairing m) (infBifun F) 0 :=
  mem_kuhnTucker_iff_neg_mem_subdifferential ht hb

/-- **Theorem 29.1**, second assertion as an equation of sets: the Kuhn–Tucker set is the reflection
of `∂(inf F)(0)`. Corollaries 29.1.1–29.1.5 are subdifferential properties transported through
it. -/
theorem theorem_29_1_set (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = -(subdifferential (pairing m) (infBifun F) 0) :=
  kuhnTucker_eq_neg_subdifferential ht hb

end Theorem291

/-! ### Corollary 29.1.1 -/

section Corollary2911

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 29.1.1**, first clause: the ε-subgradient description of the Kuhn–Tucker set, read
as a monotone family. -/
theorem corollary_29_1_1_monotone {r : ℝ} (hF : ConvexBifun F) (hr : infBifun F 0 = (r : EReal))
    (u : Rn m) :
    MonotoneOn (fun a : ℝ => (infBifun F (0 + a • u) - infBifun F 0) / (a : EReal))
      (Set.Ioi 0) :=
  monotoneOn_sub_div (convexFn_infBifun hF) hr u

/-- **Corollary 29.1.1**, the directional derivative of `inf F` at the origin, written as the
infimum the book displays. -/
theorem corollary_29_1_1_iInf (F : Bifun (Rn m) (Rn n)) (u : Rn m) :
    dirDeriv (infBifun F) 0 u
      = ⨅ a ∈ Set.Ioi (0 : ℝ), (infBifun F (0 + a • u) - infBifun F 0) / (a : EReal) :=
  dirDeriv_apply _ 0 u

/-- **Corollary 29.1.1**: `(inf F)'(0; ·)` is positively homogeneous — a reindexing of the infimum,
needing no hypothesis. -/
theorem corollary_29_1_1_posHomogeneous (F : Bifun (Rn m) (Rn n)) :
    PosHomogeneous (dirDeriv (infBifun F) 0) :=
  posHomogeneous_dirDeriv_infBifun F

/-- **Corollary 29.1.1**: `(inf F)'(0; ·)` is a convex function of the direction. -/
theorem corollary_29_1_1_convexFn (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : ConvexFn (dirDeriv (infBifun F) 0) :=
  convexFn_dirDeriv_infBifun hF ht hb

/-- **Corollary 29.1.1**, second clause: the Kuhn–Tucker vectors form a convex set. -/
theorem corollary_29_1_1_convex (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker (pairing m) F) :=
  convex_kuhnTucker ht hb

/-- **Corollary 29.1.1**, second clause: the Kuhn–Tucker vectors form a closed set. -/
theorem corollary_29_1_1_isClosed (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsClosed (KuhnTucker (pairing m) F) :=
  isClosed_kuhnTucker ht hb

/-- **Corollary 29.1.1**, last clause: the support function of the Kuhn–Tucker set is the
directional derivative of `inf F` at the origin, in the book's `-inf {⟨u*, u⟩}` form. -/
theorem corollary_29_1_1_supportFn (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) (u : Rn m) :
    supportFn (pairing m) (KuhnTucker (pairing m) F) u
      = clFn (dirDeriv (infBifun F) 0) (-u) := by
  have h := supportFn_kuhnTucker (B := pairing m) hF ht hb u
  rwa [flip_pairing] at h

end Corollary2911

/-! ### Corollary 29.1.2 -/

section Corollary2912

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 29.1.2**. At a finite optimal value a Kuhn–Tucker vector fails to exist exactly when
some direction of perturbation makes the *two-sided* directional derivative of the optimal value
`-∞`: `(inf F)'(0; u) = -∞` together with `(inf F)'(0; -u) = +∞`. In the equilibrium-price reading,
the program has one unless perturbation in some direction is "infinitely advantageous". -/
theorem corollary_29_1_2 (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = ∅ ↔
      ∃ u : Rn m, dirDeriv (infBifun F) 0 u = ⊥ ∧ dirDeriv (infBifun F) 0 (-u) = ⊤ :=
  kuhnTucker_eq_empty_iff hF ht hb

end Corollary2912

/-! ### Corollary 29.1.3 -/

section Corollary2913

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {b : Rn m}

/-- **Corollary 29.1.3**. At a finite optimal value `(P)` has a *unique* Kuhn–Tucker vector exactly
when the perturbation function is differentiable at the origin. The book's hypotheses are kept even
though its proof cites Theorem 25.1, which needs properness that "finite optimal value" does not
give: properness is free on each side, from `proper_of_mem_subdifferential` and
`HasGradientAtFn.proper`. -/
theorem corollary_29_1_3 (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (∃ v : Rn m, KuhnTucker (pairing m) F = {v}) ↔ DifferentiableAtFn (infBifun F) 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hsub : subdifferential (pairing m) (infBifun F) 0 = {-v} := by
      have h := theorem_29_1_set (F := F) ht hb
      rw [hv] at h
      have h2 : subdifferential (pairing m) (infBifun F) 0 = -({v} : Set (Rn m)) := by
        rw [h, neg_neg]
      rw [h2, Set.neg_singleton]
    have hmem : -v ∈ subdifferential (pairing m) (infBifun F) 0 := by rw [hsub]; rfl
    have hp : Proper (infBifun F) := proper_of_mem_subdifferential ht hb hmem
    exact (theorem_25_1_differentiableAtFn (convexFn_infBifun hF) hp).2 ⟨-v, hsub⟩
  · intro hd
    obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 hd
    have hp : Proper (infBifun F) := corollary_25_1_1_proper (convexFn_infBifun hF) hc
    refine ⟨-c, ?_⟩
    rw [theorem_29_1_set ht hb, theorem_25_1_forward (convexFn_infBifun hF) hc,
      Set.neg_singleton]

/-- **Corollary 29.1.3**, the formula: where the perturbation function is differentiable at the
origin with gradient `b`, the unique Kuhn–Tucker vector is `-b`. -/
theorem corollary_29_1_3_eq (hF : ConvexBifun F) (h : HasGradientVecAt (infBifun F) b 0)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (pairing m) F = {-b} := by
  rw [theorem_29_1_set ht hb, theorem_25_1_forward (convexFn_infBifun hF) h, Set.neg_singleton]

/-- **Corollary 29.1.3**, the value of the gradient: the unique Kuhn–Tucker vector is
`-∇(inf F)(0)`, coordinate by coordinate. -/
theorem corollary_29_1_3_partial (hF : ConvexBifun F) {v : Rn m}
    (hv : v ∈ KuhnTucker (pairing m) F) (hd : DifferentiableAtFn (infBifun F) 0) (i : Fin m) :
    dirDeriv (infBifun F) 0 (EuclideanSpace.single i (1 : ℝ)) = ((-(v i) : ℝ) : EReal) := by
  obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 hd
  have hset : KuhnTucker (pairing m) F = {-c} :=
    corollary_29_1_3_eq hF hc hv.1 hv.2.1
  have hvc : v = -c := by rw [hset] at hv; exact hv
  rw [theorem_25_2_dirDeriv (convexFn_infBifun hF) hc, hvc]
  congr 1
  rw [pairing_apply, EuclideanSpace.inner_single_left]
  simp

end Corollary2913

/-! ### Strong and strict consistency -/

section Consistency

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- `(P)` is strictly consistent iff for every `u` there is a `λ > 0` with `λu ∈ dom F` — a
consistent program is strictly consistent unless some perturbation empties the feasible set at
once. -/
theorem strictlyConsistent_iff (hF : ConvexBifun F) :
    StrictlyConsistent F ↔ ∀ u : Rn m, ∃ a : ℝ, 0 < a ∧ a • u ∈ domBifun F := by
  rw [StrictlyConsistent, Convex.mem_interior_iff_absorbs (convex_domBifun hF)]
  exact forall_congr' fun u => exists_congr fun a => by rw [zero_add]

end Consistency

/-! ### Corollary 29.1.4 -/

section Corollary2914

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

private theorem iSup_coe_neg_eq (S : Set (Rn m)) (g : Rn m → ℝ) :
    (⨆ v ∈ S, ((-(g v) : ℝ) : EReal)) = -(⨅ v ∈ S, ((g v : ℝ) : EReal)) := by
  rw [EReal.neg_iInf]
  refine iSup_congr fun v => ?_
  rw [EReal.neg_iInf]
  exact iSup_congr fun _ => (EReal.coe_neg (g v)).symm

/-- **Corollary 29.1.4**, existence half: a strongly consistent convex program with a finite optimal
value has a Kuhn–Tucker vector. Theorem 23.4 applied to `inf F`, proper by Theorem 7.2. -/
theorem corollary_29_1_4_nonempty (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_stronglyConsistent hF
    (proper_infBifun_of_stronglyConsistent hF hs hb) hs ht

/-- **Corollary 29.1.4**, the formula: the directional derivative of the optimal value at `0` is
`-inf {⟨u*, u⟩ | u* a Kuhn–Tucker vector}`. -/
theorem corollary_29_1_4_dirDeriv (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) (u : Rn m) :
    dirDeriv (infBifun F) 0 u
      = -(⨅ v ∈ KuhnTucker (pairing m) F, ((pairing m u v : ℝ) : EReal)) := by
  have hp : Proper (infBifun F) := proper_infBifun_of_stronglyConsistent hF hs hb
  rw [dirDeriv_infBifun_eq (B := pairing m) hF hp hs u, flip_pairing, supportFn_apply,
    ← iSup_coe_neg_eq]
  refine iSup_congr fun v => iSup_congr fun _ => ?_
  rw [map_neg, pairing_comm v u]

end Corollary2914

/-! ### Corollary 29.1.5 -/

section Corollary2915

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 29.1.5**, first clause: for a strictly consistent program with a finite optimal
value `inf F` is finite and continuous on the open convex neighbourhood `int (dom F)` of `0`. -/
theorem corollary_29_1_5_nbhd (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) :
    ∃ V : Set (Rn m), IsOpen V ∧ Convex ℝ V ∧ (0 : Rn m) ∈ V ∧
      (∀ u ∈ V, infBifun F u ≠ ⊤ ∧ infBifun F u ≠ ⊥) ∧ ContinuousOn (infBifun F) V := by
  have hp : Proper (infBifun F) :=
    proper_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb
  refine ⟨interior (domBifun F), isOpen_interior, (convex_domBifun hF).interior, hs,
    fun u hu => ⟨infBifun_ne_top_of_mem_domBifun (interior_subset hu), hp.ne_bot u⟩,
    continuousOn_infBifun_interior hF hp⟩

/-- **Corollary 29.1.5**, last clause: the Kuhn–Tucker vectors form a **non-empty** set. -/
theorem corollary_29_1_5_nonempty (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_strictlyConsistent hF
    (proper_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs ht

/-- **Corollary 29.1.5**, last clause: the Kuhn–Tucker vectors form a **closed** set. -/
theorem corollary_29_1_5_isClosed (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsClosed (KuhnTucker (pairing m) F) :=
  corollary_29_1_1_isClosed ht hb

/-- **Corollary 29.1.5**, last clause: the Kuhn–Tucker vectors are **bounded**. This is what
distinguishes Corollary 29.1.5 from Corollary 29.1.4: under mere *strong* consistency the
Kuhn–Tucker set need not be bounded, Theorem 23.4 bounding `∂f x` only at interior points. -/
theorem corollary_29_1_5_isBounded (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) : Bornology.IsBounded (KuhnTucker (pairing m) F) :=
  isBounded_kuhnTucker_of_strictlyConsistent hF
    (proper_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs

/-- **Corollary 29.1.5**, last clause: the Kuhn–Tucker vectors form a **convex** set. -/
theorem corollary_29_1_5_convex (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker (pairing m) F) :=
  corollary_29_1_1_convex ht hb

/-- **Corollary 29.1.5**, last clause in one piece: for a strictly consistent program with a finite
optimal value the Kuhn–Tucker set is non-empty, compact and convex. -/
theorem corollary_29_1_5_isCompact (hF : ConvexBifun F) (hs : StrictlyConsistent F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    IsCompact (KuhnTucker (pairing m) F) :=
  isCompact_kuhnTucker_of_strictlyConsistent hF
    (proper_infBifun_of_stronglyConsistent hF hs.stronglyConsistent hb) hs ht

end Corollary2915

/-! ### Corollary 29.1.6 -/

section Corollary2916

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 29.1.6**: if `inf Fu = -∞` for *some* `u`, then `inf Fu = -∞` for *every*
`u ∈ ri (dom F)`. -/
theorem corollary_29_1_6_bot (hF : ConvexBifun F) (h : ∃ u : Rn m, infBifun F u = ⊥) {u : Rn m}
    (hu : u ∈ ri (domBifun F)) : infBifun F u = ⊥ :=
  infBifun_eq_bot_of_mem_relint hF h hu

/-- **Corollary 29.1.6**, the parenthesis: `inf Fu = +∞` for `u ∉ dom F`. Needs neither convexity
nor the corollary's hypothesis; it is Theorem 29.1's `dom (inf F) = dom F`. -/
theorem corollary_29_1_6_top {u : Rn m} (hu : u ∉ domBifun F) : infBifun F u = ⊤ :=
  infBifun_eq_top_of_notMem_domBifun hu

end Corollary2916

/-! ### Theorem 29.2 -/

section Theorem292

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Theorem 29.2**, first clause: every slice `Fu` of a polyhedral convex bifunction — the
objective function `F0` in particular — is a polyhedral convex function. -/
theorem theorem_29_2_objective (hF : PolyhedralBifun F) (u : Rn m) : PolyhedralFn (F u) :=
  hF.polyhedralFn_apply u

/-- **Theorem 29.2**, second clause: the perturbation function of a polyhedral convex program is
polyhedral — Corollary 19.3.1 at the projection `(u, x) ↦ u`. -/
theorem theorem_29_2_infBifun (hF : PolyhedralBifun F) : PolyhedralFn (infBifun F) :=
  hF.polyhedralFn_infBifun

/-- **Theorem 29.2**, third clause: a polyhedral convex program with a finite optimal value has an
**optimal solution**. Less is needed than the book asks — `inf F0 ≠ -∞` alone bounds `F0` below and
Corollary 27.3.2 attains the infimum; finiteness is what the polyhedrality clause below needs. -/
theorem theorem_29_2_argmin_nonempty (hF : PolyhedralBifun F) (hb : infBifun F 0 ≠ ⊥) :
    (argmin (F 0)).Nonempty :=
  argmin_nonempty_of_polyhedralBifun hF hb

/-- **Theorem 29.2**, third clause: a polyhedral convex program with a finite optimal value has at
least one **Kuhn–Tucker vector**, by Theorem 23.10 applied to `inf F` at the origin. -/
theorem theorem_29_2_kuhnTucker_nonempty (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : (KuhnTucker (pairing m) F).Nonempty :=
  kuhnTucker_nonempty_of_polyhedralBifun hF ht hb

/-- **Theorem 29.2**, last clause: the optimal solutions form a polyhedral convex set, being a
sublevel set of the polyhedral `F0` at the optimal value. -/
theorem theorem_29_2_polyhedral_argmin (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : Polyhedral (argmin (F 0)) :=
  polyhedral_argmin_of_polyhedralBifun hF ht hb

/-- **Theorem 29.2**, last clause: the Kuhn–Tucker vectors form a polyhedral convex set. -/
theorem theorem_29_2_polyhedral_kuhnTucker (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : Polyhedral (KuhnTucker (pairing m) F) :=
  polyhedral_kuhnTucker_of_polyhedralBifun hF ht hb

end Theorem292

/-! ### Theorem 29.3 -/

section Theorem293

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {v : Rn m} {x : Rn n}

/-- **Theorem 29.3**, as the book displays it: for a closed proper convex bifunction, `ū*` is a
Kuhn–Tucker vector and `x̄` an optimal solution iff `L(u*, x̄) ≤ L(ū*, x̄) ≤ L(ū*, x)` for all `u*`
and all `x` — that is, iff `(ū*, x̄)` is a saddle-point of the Lagrangian. -/
theorem theorem_29_3 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F)) :
    ((∀ w : Rn m, lagrangian (pairing m) F w x ≤ lagrangian (pairing m) F v x) ∧
        ∀ y : Rn n, lagrangian (pairing m) F v x ≤ lagrangian (pairing m) F v y)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [← isSaddlePoint_lagrangian_iff_forall, isSaddlePoint_lagrangian_iff hF hcl hpr]
  refine and_congr_right fun hv => ?_
  exact (isOptimalSolution_iff_mem_argmin (fun y => hpr.ne_bot (0, y)) hv.1).symm

/-- **Theorem 29.3**, in the backbone's bundled form. -/
theorem theorem_29_3_isSaddlePoint (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [isSaddlePoint_lagrangian_iff_forall]
  exact theorem_29_3 hF hcl hpr

end Theorem293

/-! ### Corollary 29.3.1 -/

section Corollary2931

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- The common core of Corollary 29.3.1's three constraint qualifications: whenever one supplies a
Kuhn–Tucker vector at a finite optimal value, optimality of `x̄` is equivalent to `x̄` completing
some `ū*` to a saddle-point. At optimal value `-∞` both sides are false. -/
private theorem corollary_29_3_1_aux (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hc : Consistent F)
    (hkt : infBifun F 0 ≠ ⊥ → (KuhnTucker (pairing m) F).Nonempty) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) := by
  by_cases hb : infBifun F 0 = ⊥
  · refine ⟨fun h => absurd h (not_isOptimalSolution_of_infBifun_eq_bot hb), ?_⟩
    rintro ⟨v, hv⟩
    exact absurd ((theorem_29_3_isSaddlePoint hF hcl hpr).1 hv).1.2.1 (not_not.2 hb)
  · have ht : infBifun F 0 ≠ ⊤ := infBifun_ne_top_of_mem_domBifun hc
    rw [isOptimalSolution_iff_mem_argmin (fun y => hpr.ne_bot (0, y)) ht]
    exact mem_argmin_iff_exists_isSaddlePoint_lagrangian hF hcl hpr (hkt hb)

/-- **Corollary 29.3.1**, the strongly consistent case: `x̄` is an optimal solution exactly when it
completes some `ū*` to a saddle-point of the Lagrangian. -/
theorem corollary_29_3_1_stronglyConsistent (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hs : StronglyConsistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_aux hF hcl hpr hs.consistent fun hb =>
    corollary_29_1_4_nonempty hF hs (infBifun_ne_top_of_mem_domBifun hs.consistent) hb

/-- **Corollary 29.3.1**, the strictly consistent case. A strictly consistent program is strongly
consistent, so this is the previous corollary verbatim. -/
theorem corollary_29_3_1_strictlyConsistent (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hs : StrictlyConsistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_stronglyConsistent hF hcl hpr hs.stronglyConsistent

/-- **Corollary 29.3.1**, the polyhedral case: for a *polyhedral* closed proper convex program plain
consistency suffices, Theorem 29.2 supplying a Kuhn–Tucker vector with no interiority hypothesis. -/
theorem corollary_29_3_1_polyhedral (hF : PolyhedralBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hc : Consistent F) :
    IsOptimalSolution F x ↔
      ∃ v : Rn m, IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) :=
  corollary_29_3_1_aux hF.convexBifun hcl hpr hc fun hb =>
    theorem_29_2_kuhnTucker_nonempty hF (infBifun_ne_top_of_mem_domBifun hc) hb

end Corollary2931

/-! ### Theorem 29.4

`cl F`, the bifunction whose graph function is `cl (graph F)`, regularizes a program before
Theorem 29.3 or §30's duality theory is applied to it. -/

section Theorem294

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- `cl F` is a closed convex bifunction, and proper when `F` is. -/
theorem clBifun_convex (hF : ConvexBifun F) : ConvexBifun (clBifun F) :=
  ConvexBifun.clBifun hF

/-- `cl F` is closed, for any `F`. -/
theorem clBifun_closed (F : Bifun (Rn m) (Rn n)) : ClosedBifun (clBifun F) :=
  closedBifun_clBifun F

/-- `cl F` is proper when `F` is. -/
theorem clBifun_proper (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    Proper (graphFn (clBifun F)) :=
  ConvexFn.proper_clFn hF hp

/-- **Theorem 29.4**, first assertion: `(cl F)u = cl (Fu)` for each `u ∈ ri (dom F)`. Rockafellar's
closure of an improper convex function that is somewhere `-∞` is the constant `-∞` everywhere, not
the lower semicontinuous hull `f̄`; both proofs turn on that convention. -/
theorem theorem_29_4_apply (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (domBifun F)) :
    clBifun F u = clFn (F u) :=
  clBifun_apply_eq_clFn hF hu

/-- **Theorem 29.4**, second assertion: `inf (cl F)u = inf Fu` for `u ∈ ri (dom F)`. A convex
function and its closure have the same infimum, so the content is the first assertion. -/
theorem theorem_29_4_inf (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (domBifun F)) :
    infBifun (clBifun F) u = infBifun F u :=
  infBifun_clBifun_eq hF hu

/-- **Theorem 29.4**, third assertion, first inclusion: `dom F ⊆ dom (cl F)` for proper `F`. -/
theorem theorem_29_4_dom_subset (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    domBifun F ⊆ domBifun (clBifun F) :=
  domBifun_subset_domBifun_clBifun hF hp

/-- **Theorem 29.4**, third assertion, second inclusion: `dom (cl F) ⊆ cl (dom F)` for proper `F`.
Properness is not decoration: `originBifun` below has `dom F = {0}` and `dom (cl F) = ℝ¹`. -/
theorem theorem_29_4_dom_subset_closure (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    domBifun (clBifun F) ⊆ closure (domBifun F) :=
  domBifun_clBifun_subset_closure hF hp

end Theorem294

/-! ### Corollary 29.4.1 -/

section Corollary2941

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- **Corollary 29.4.1**, the underlying domain fact: closing a proper convex bifunction leaves
`ri (dom F)` alone. Theorem 29.4 sandwiches `dom (cl F)` between `dom F` and `cl (dom F)`, and
Corollary 6.3.1 says such a sandwich has the same relative interior. -/
theorem corollary_29_4_1_relint (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    ri (domBifun (clBifun F)) = ri (domBifun F) :=
  relint_domBifun_clBifun hF hp

/-- **Corollary 29.4.1**, first clause: if `(P)` is strongly consistent then so is `(cl P)`. This
clause **does** survive without properness: an improper `F` whose graph function is somewhere `-∞`
has `dom (cl F) = ℝᵐ`, and one with empty graph domain is not consistent at all. -/
theorem corollary_29_4_1_stronglyConsistent (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    StronglyConsistent (clBifun F) := by
  by_cases hp : Proper (graphFn F)
  · exact stronglyConsistent_clBifun hF hp hs
  · have hne : (dom (graphFn F)).Nonempty := by
      have h0 : (0 : Rn m) ∈ domBifun F := intrinsicInterior_subset hs
      obtain ⟨x, hx⟩ := h0
      exact ⟨(0, x), mem_dom.2 (lt_of_le_of_ne le_top hx)⟩
    have hbot : ∃ p, graphFn F p = ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hp ⟨hne, hcon⟩
    obtain ⟨p, hpbot⟩ := hbot
    have hlsc : lscHull (graphFn F) p = ⊥ :=
      le_bot_iff.1 (le_trans (lscHull_le (graphFn F) p) (le_of_eq hpbot))
    have hcl : clFn (graphFn F) = fun _ => ⊥ := clFn_of_exists_eq_bot ⟨p, hlsc⟩
    have hdom : domBifun (clBifun F) = Set.univ := by
      ext u
      simp only [mem_domBifun, Set.mem_univ, iff_true]
      exact ⟨0, by rw [clBifun_apply, hcl]; simp⟩
    change (0 : Rn m) ∈ ri (domBifun (clBifun F))
    rw [hdom]
    exact interior_subset_intrinsicInterior (by simp)

/-- **Corollary 29.4.1**, second clause: the objective function for `(cl P)` is the closure of the
objective function for `(P)`. This is Theorem 29.4 read at the origin. -/
theorem corollary_29_4_1_objective (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    clBifun F 0 = clFn (F 0) :=
  clBifun_zero_eq_clFn hF hs

/-- **Corollary 29.4.1**, third clause: `(P)` and `(cl P)` have the same optimal value. -/
theorem corollary_29_4_1_optimalValue (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    infBifun (clBifun F) 0 = infBifun F 0 :=
  infBifun_clBifun_zero_eq hF hs

/-- **Corollary 29.4.1**, fourth clause, in the backbone's vocabulary: every minimiser of `F0`
minimises `(cl F)0`. The inclusion is strict in general — closing can create new minimisers. -/
theorem corollary_29_4_1_argmin (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    argmin (F 0) ⊆ argmin (clBifun F 0) :=
  argmin_subset_argmin_clBifun hF hs

/-- **Corollary 29.4.1**, fourth clause, in the book's own vocabulary: every optimal solution to
`(P)` is an optimal solution to `(cl P)`. -/
theorem corollary_29_4_1_optimalSolution (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (h : IsOptimalSolution F x) : IsOptimalSolution (clBifun F) x := by
  have hval : infBifun (clBifun F) 0 = infBifun F 0 := infBifun_clBifun_zero_eq hF hs
  have hge : infBifun (clBifun F) 0 ≤ clBifun F 0 x := by
    rw [infBifun_apply]
    exact iInf_le _ x
  have hle : clBifun F 0 x ≤ infBifun (clBifun F) 0 := by
    rw [hval, ← h.2.2]
    exact clBifun_le F 0 x
  have heq : clBifun F 0 x = infBifun (clBifun F) 0 := le_antisymm hle hge
  refine ⟨?_, ?_, heq⟩
  · rw [heq, hval, ← h.2.2]; exact h.1
  · rw [heq, hval, ← h.2.2]; exact h.2.1

/-- **Corollary 29.4.1**, fifth clause, **with the properness hypothesis the book omits**: the
perturbation functions of `(P)` and `(cl P)` agree on a neighbourhood of `0`. Theorem 29.4 gives
agreement only on `ri (dom F)`; what upgrades it is `dom (cl F) ⊆ cl (dom F) ⊆ aff (dom F)`, so a
small enough ball meets only `ri (dom F)` and points off `aff (dom F)` where both are `+∞`. That
inclusion is where properness enters — see `corollary_29_4_1_perturbation_false`. -/
theorem corollary_29_4_1_eventually (hF : ConvexBifun F) (hp : Proper (graphFn F))
    (hs : StronglyConsistent F) :
    ∀ᶠ u in 𝓝 (0 : Rn m), infBifun (clBifun F) u = infBifun F u :=
  eventually_infBifun_clBifun_eq hF hp hs

/-- **Corollary 29.4.1**, last clause: `(P)` and `(cl P)` have the same Kuhn–Tucker vectors. The
book deduces this from the perturbation clause, which needs properness; the route here does not,
since the adjoint bifunction never sees the closure (`adjointBifun_clBifun`). -/
theorem corollary_29_4_1_kuhnTucker (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    KuhnTucker (pairing m) (clBifun F) = KuhnTucker (pairing m) F :=
  kuhnTucker_clBifun_eq (Bu := pairing m) (pairing n) hF hs

end Corollary2941

/-! ### Corollary 29.4.1 as printed is false

`corollary_29_4_1_perturbation` transcribes the corollary's fifth clause with the hypotheses the
book prints, and `corollary_29_4_1_perturbation_false` refutes it on `ℝ¹`. -/

section Counterexample

/-- The counterexample to Corollary 29.4.1 as printed: the bifunction on `ℝ¹` that is `-∞` when
`u = 0` and `+∞` otherwise. What the example must do is make `dom F` a proper affine subset with the
origin in its relative interior, and `{0} ⊆ ℝ¹` is the cheapest such set. -/
noncomputable def originBifun : Bifun (Rn 1) (Rn 1) := fun u _ => ⨆ _ : u ≠ 0, (⊤ : EReal)

@[simp] theorem originBifun_zero (x : Rn 1) : originBifun 0 x = ⊥ := by
  rw [originBifun, iSup_neg (by simp)]

@[simp] theorem originBifun_of_ne_zero {u : Rn 1} (hu : u ≠ 0) (x : Rn 1) :
    originBifun u x = ⊤ := by
  rw [originBifun, iSup_pos hu]

/-- `originBifun` is convex: its epigraph is the preimage of `{0}` under a linear map, hence a
linear subspace of `(ℝ¹ × ℝ¹) × ℝ`. -/
theorem convexBifun_originBifun : ConvexBifun originBifun := by
  refine ⟨?_⟩
  have hepi : epi (graphFn originBifun)
      = ((LinearMap.fst ℝ (Rn 1) (Rn 1)) ∘ₗ
          (LinearMap.fst ℝ (Rn 1 × Rn 1) ℝ)) ⁻¹' ({0} : Set (Rn 1)) := by
    ext q
    obtain ⟨⟨u, y⟩, a⟩ := q
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · simp [hu]
  rw [hepi]
  exact (convex_singleton (0 : Rn 1)).linear_preimage _

/-- `dom F = {0}`. -/
@[simp] theorem domBifun_originBifun : domBifun originBifun = ({0} : Set (Rn 1)) := by
  ext u
  simp only [mem_domBifun, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy⟩
    by_contra hu
    exact hy (originBifun_of_ne_zero hu y)
  · rintro rfl
    exact ⟨0, by simp⟩

/-- `(P)` is strongly consistent: `ri {0} = {0}` contains the origin. -/
theorem stronglyConsistent_originBifun : StronglyConsistent originBifun := by
  change (0 : Rn 1) ∈ ri (domBifun originBifun)
  rw [domBifun_originBifun, intrinsicInterior_singleton]
  exact rfl

/-- `cl F` is the constant `-∞`: the graph function takes the value `-∞`, and Rockafellar's closure
convention makes the closure of such a function the constant `-∞` everywhere. -/
theorem clBifun_originBifun (u x : Rn 1) : clBifun originBifun u x = ⊥ := by
  have hlsc : lscHull (graphFn originBifun) ((0 : Rn 1), (0 : Rn 1)) = ⊥ := by
    refine le_bot_iff.1 (le_trans (lscHull_le (graphFn originBifun) _) (le_of_eq ?_))
    rw [graphFn_apply, originBifun_zero]
  rw [clBifun_apply, clFn_of_exists_eq_bot ⟨_, hlsc⟩]

/-- `inf (cl F) ≡ -∞`. -/
theorem infBifun_clBifun_originBifun (u : Rn 1) : infBifun (clBifun originBifun) u = ⊥ := by
  rw [infBifun_apply]
  exact le_bot_iff.1 (le_trans (iInf_le _ 0) (le_of_eq (clBifun_originBifun u 0)))

/-- `inf F = +∞` away from the origin. -/
theorem infBifun_originBifun_of_ne_zero {u : Rn 1} (hu : u ≠ 0) : infBifun originBifun u = ⊤ := by
  rw [infBifun_apply]
  simp [originBifun_of_ne_zero hu]

/-- **Corollary 29.4.1's perturbation clause with the hypotheses the book prints**: "Let `F` be a
convex bifunction from `Rᵐ` to `Rⁿ`. … Assume that `(P)` is strongly consistent. … The perturbation
functions for `(P)` and `(cl P)` agree on a neighborhood of `0`." No properness anywhere. -/
def corollary_29_4_1_perturbation : Prop :=
  ∀ (m n : ℕ) (F : Bifun (Rn m) (Rn n)), ConvexBifun F → StronglyConsistent F →
    ∀ᶠ u in 𝓝 (0 : Rn m), infBifun (clBifun F) u = infBifun F u

/-- **Corollary 29.4.1 is false as Rockafellar states it.**

Take `F = originBifun` on `ℝ¹`: `(Fu)(x) = -∞` for `u = 0` and `+∞` for `u ≠ 0`. It is convex and
`dom F = {0}` has `0` in its relative interior, so `(P)` is strongly consistent; but its graph
function takes the value `-∞`, so `cl (graph F)` is the constant `-∞` and `inf (cl F) ≡ -∞`, while
`inf F = +∞` at every `u ≠ 0`. The two perturbation functions agree at the single point `0`.

Every other clause is Theorem 29.4 read at the origin, where `0 ∈ ri (dom F)` is available; this
one needs agreement *outside* `ri (dom F)`, which only `dom (cl F) ⊆ cl (dom F)` supplies, and that
is stated for proper `F`. With `F` proper the clause is `corollary_29_4_1_eventually`. -/
theorem corollary_29_4_1_perturbation_false : ¬ corollary_29_4_1_perturbation := by
  intro hcor
  have hev := hcor 1 1 originBifun convexBifun_originBifun stronglyConsistent_originBifun
  have h1 : ∀ᶠ u in 𝓝[≠] (0 : Rn 1),
      infBifun (clBifun originBifun) u = infBifun originBifun u :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨u, hu, hune⟩ := (h1.and (eventually_mem_nhdsWithin (a := (0 : Rn 1)))).exists
  have hune' : u ≠ 0 := hune
  rw [infBifun_clBifun_originBifun u, infBifun_originBifun_of_ne_zero hune'] at hu
  exact absurd hu (by simp)

end Counterexample

end Rockafellar
