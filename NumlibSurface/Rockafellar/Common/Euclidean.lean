import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Duality.GaugeLike
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.EuclideanProd
import Numlib.Analysis.Convex.HullDirections
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Recession.Cone
import Numlib.Analysis.Convex.Simplicial
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.LinearAlgebra.Subspace
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.TFAE

/-!
# Rockafellar: the Euclidean vocabulary of the surface

Shared notation and glue lemmas for the surface library of R. Tyrrell Rockafellar, *Convex
Analysis*, Princeton University Press, 1970.

This module is not a section of the book. It is the vocabulary in which a book written in `ℝⁿ` is
transcribed, and every section module of `NumlibSurface.Rockafellar` is stated in it: `Rn n` is
`EuclideanSpace ℝ (Fin n)` and `pairing n` is its own inner product read as a bilinear map.
Together they instantiate the backbone's duality theory at a stroke, which is why the book can
state everything without qualification. Everything general about a self-pairing of inner-product
type lives in the backbone (`Numlib/Analysis/Convex/Duality/InnerPairing.lean`); what is here is
the `ℝⁿ` spelling of it, in the flat `Rockafellar` namespace the rest of the library uses.

## Main definitions

* `Rn n` — the ambient space.
* `pairing n` — the self-pairing `⟨x, y⟩`, as a `LinearMap` so that the backbone's duality applies.
* `pairingProd`, `pairingAdjoint` — the pairing on a product, and its sign-flipped form.
* `linFn b` — the vector `b` read as the linear function `⟨·, b⟩`, an abbreviation of Mathlib's
  `innerSL ℝ b` in the book's spelling.

## Main results

* `flip_pairing` — the pairing is its own flip, which rewrites away the `.flip` a bipolar theorem
  hands back.
* `pairing_comm`, `forall_pairing_le_comm`, `forall_pairing_lt_comm` — a book writes a linear
  system as `⟨aᵢ, x⟩ ≤ αᵢ` and the backbone puts the variable on the left; these translate.
* `pairing_eq_sum`, `pairing_two` — the pairing in coordinates.
* `exists_linFn`, `linFn_eq_toDual`, `linFn_eq_zero_iff`, `toDual_apply_eq_pairing`,
  `separatingRight_pairing` — the backbone's Fréchet–Riesz and separation facts about `innerₗ E`,
  restated for `pairing n` and `linFn`.
* `pairingProd_euclideanProdEquiv` — `pairingProd` is the inner product of `Rn (m + n)`, read
  through the concatenation of coordinates.

## Implementation notes

A textbook in `ℝⁿ` identifies a space with its dual, writing `x*` for a vector of the same space.
Both sides of `pairing n` are `Rn n`, so the book's `*` is a naming convention here and not a type
distinction. The backbone keeps its two spaces apart precisely so that the general theory cannot
use self-duality silently.
-/

namespace Rockafellar

open ConvexAnalysis

/-- The ambient space of a finite-dimensional real surface: `ℝⁿ` with its Euclidean structure. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The **standard inner product** on `Rn n`, as a bilinear map, which is the form the backbone's
duality theory takes. A book that writes `⟨x, x*⟩` for vectors of one space means this. An
`abbrev`, not a `def`: instance search does not unfold a plain `def`, and every pairing class the
surface needs is stated about `innerₗ`. -/
noncomputable abbrev pairing (n : ℕ) : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ := innerₗ (Rn n)

@[simp] theorem pairing_apply {n : ℕ} (x y : Rn n) : pairing n x y = inner ℝ x y := rfl

/-- The pairing is symmetric, hence its own flip: every backbone statement that asks for `B.flip`
is asking for `pairing n` again. -/
@[simp] theorem flip_pairing (n : ℕ) : (pairing n).flip = pairing n :=
  flip_eq_self (pairing n)

/-- **The pairing is symmetric.** Rockafellar writes a linear system as `⟨aᵢ, x⟩ ≤ αᵢ`, with the
data on the left; the backbone's `B x y` puts the variable there. -/
theorem pairing_comm {n : ℕ} (x y : Rn n) : pairing n x y = pairing n y x := real_inner_comm y x

/-- A system of weak inequalities read in the book's orientation and in the backbone's. -/
theorem forall_pairing_le_comm {n : ℕ} {ι : Sort*} (a : ι → Rn n) (α : ι → ℝ) (x : Rn n) :
    (∀ i, pairing n (a i) x ≤ α i) ↔ ∀ i, pairing n x (a i) ≤ α i :=
  forall_congr' fun i => by rw [pairing_comm]

/-- A system of strict inequalities read in the book's orientation and in the backbone's. -/
theorem forall_pairing_lt_comm {n : ℕ} {ι : Sort*} (a : ι → Rn n) (α : ι → ℝ) (x : Rn n) :
    (∀ i, pairing n (a i) x < α i) ↔ ∀ i, pairing n x (a i) < α i :=
  forall_congr' fun i => by rw [pairing_comm]

/-- **The pairing in coordinates**: `⟨u, v⟩ = ∑ᵢ uᵢ vᵢ`. -/
theorem pairing_eq_sum {n : ℕ} (u v : Rn n) : pairing n u v = ∑ i, u i * v i := by
  simp only [pairing_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The pairing on `ℝ²` in coordinates**: `⟨u, v⟩ = u₀v₀ + u₁v₁`. Rockafellar's counterexamples
are two-dimensional almost without exception, and this is the first line of every one of them. -/
theorem pairing_two (u v : Rn 2) : pairing 2 u v = u 0 * v 0 + u 1 * v 1 := by
  rw [pairing_eq_sum, Fin.sum_univ_two]

/-- **Each coordinate of `Rn n` is continuous**, `Rn n` being a `PiLp 2`. A counterexample that
cuts a region out of `Rn n` with coordinate inequalities needs this to see the region is open. -/
theorem continuous_coord {n : ℕ} (i : Fin n) : Continuous fun x : Rn n => x i :=
  PiLp.continuous_apply (p := 2) (fun _ : Fin n => ℝ) i

/-- **`pairing n` separates on the right**, which is the hypothesis the backbone's level-set and
recession duality asks for in place of a book's `y ≠ 0`. -/
theorem separatingRight_pairing (n : ℕ) : (pairing n).SeparatingRight :=
  separatingRight_innerL

/-- The **product pairing** on `Rn m × Rn n`, which is what a bifunction from `ℝᵐ` to `ℝⁿ` is
conjugated against. -/
noncomputable abbrev pairingProd (m n : ℕ) : (Rn m × Rn n) →ₗ[ℝ] (Rn m × Rn n) →ₗ[ℝ] ℝ :=
  prodPairing (pairing m) (pairing n)

/-- The **sign-flipped product pairing** of §30: the one Rockafellar's adjoint `F*` of a convex
bifunction is stated against. -/
noncomputable abbrev pairingAdjoint (m n : ℕ) : (Rn m × Rn n) →ₗ[ℝ] (Rn m × Rn n) →ₗ[ℝ] ℝ :=
  negFst (pairingProd m n)

/-- **The product pairing is the pairing of `Rn (m + n)`, read through the concatenation of
coordinates** (`euclideanProdEquiv`). This is the identification a text in `ℝⁿ` makes silently
whenever it writes a point of `ℝᵐ × ℝⁿ` as a point of `ℝᵐ⁺ⁿ`. -/
theorem pairingProd_euclideanProdEquiv {m n : ℕ} (p q : Rn m × Rn n) :
    pairingProd m n p q = pairing (m + n) (euclideanProdEquiv m n p) (euclideanProdEquiv m n q) :=
  (inner_euclideanProdEquiv p q).symm

/-! ### Dimension

`Module.finrank ℝ (Rn n) = n` is `finrank_euclideanSpace_fin`, which Mathlib does not mark `simp`;
every dimension count the surface states needs it. -/

attribute [simp] finrank_euclideanSpace_fin

/-! ### Instance discharge

Each `example` asserts that a class the surface needs is found by instance search with no
hypothesis. They are the regression test for the instantiation. -/

section Instances

variable {m n : ℕ}

-- Ambient structure on `Rn n`.
noncomputable example : NormedAddCommGroup (Rn n) := inferInstance
noncomputable example : InnerProductSpace ℝ (Rn n) := inferInstance
noncomputable example : NormedSpace ℝ (Rn n) := inferInstance
example : FiniteDimensional ℝ (Rn n) := inferInstance
example : CompleteSpace (Rn n) := inferInstance
example : ProperSpace (Rn n) := inferInstance
example : T2Space (Rn n) := inferInstance
example : LocallyConvexSpace ℝ (Rn n) := inferInstance
example : IsTopologicalAddGroup (Rn n) := inferInstance
example : ContinuousSMul ℝ (Rn n) := inferInstance
example : TopologicalSpace.SeparableSpace (Rn n) := inferInstance
example : SeparatingDual ℝ (Rn n) := inferInstance

-- The self-pairing, and the flips the backbone asks for.
example : IsInnerPairing (pairing n) := inferInstance
example : IsContinuousInnerPairing (pairing n) := inferInstance
example : IsContinuousPairing (pairing n) := inferInstance
example : IsCompatiblePairing (pairing n) := inferInstance
example : IsContinuousPairing (pairing n).flip := inferInstance
example : IsCompatiblePairing (pairing n).flip := inferInstance
example : IsCompatiblePairing (pairing n).flip.flip := inferInstance

-- Negated pairings: §34 and §37 conjugate against these.
example : IsContinuousPairing (-pairing n) := inferInstance
example : IsCompatiblePairing (-pairing n) := inferInstance
example : IsCompatiblePairing (-pairing n).flip := inferInstance

-- Product pairings: §29–§30, §37.
example : IsInnerPairing (pairingProd m n) := inferInstance
example : IsContinuousPairing (pairingProd m n) := inferInstance
example : IsCompatiblePairing (pairingProd m n) := inferInstance
example : IsContinuousPairing (pairingProd m n).flip := inferInstance
example : IsCompatiblePairing (pairingProd m n).flip := inferInstance

-- The adjoint pairing of §30.
example : IsContinuousPairing (pairingAdjoint m n) := inferInstance
example : IsCompatiblePairing (pairingAdjoint m n) := inferInstance
example : IsContinuousPairing (pairingAdjoint m n).flip := inferInstance
example : IsCompatiblePairing (pairingAdjoint m n).flip := inferInstance

end Instances

/-! ### The vector picture of a linear function

A book writes a linear function on `ℝⁿ` as `⟨·, b⟩` and quantifies over the vector `b`; the
backbone quantifies over a continuous linear functional, which is what separation produces. The
translation is Mathlib's `innerSL ℝ b`, here under the book's name `linFn b`; the facts about it
are the backbone's, restated. -/

section LinFn

variable {n : ℕ}

/-- The vector `b` read as the linear function `⟨·, b⟩`: Mathlib's `innerSL ℝ b`. -/
noncomputable abbrev linFn (b : Rn n) : Rn n →L[ℝ] ℝ := innerSL ℝ b

@[simp] theorem linFn_apply (b x : Rn n) : linFn b x = pairing n x b := by
  simp only [linFn, innerSL_apply_apply, pairing_apply]
  exact real_inner_comm x b

/-- `⟨·, b⟩` is the zero function exactly when `b` is the zero vector: this is what makes `b ≠ 0`
and "`{x | ⟨x, b⟩ = β}` is a hyperplane" the same condition. -/
theorem linFn_eq_zero_iff {b : Rn n} : linFn b = 0 ↔ b = 0 :=
  innerSL_eq_zero_iff

/-- **Every continuous linear function on `ℝⁿ` is `⟨·, b⟩`.** This Fréchet–Riesz identification is
what lets a surface statement quantify over vectors while its proof quantifies over functionals. -/
theorem exists_linFn (f : Rn n →L[ℝ] ℝ) : ∃ b : Rn n, linFn b = f :=
  exists_innerSL_eq f

/-- **`linFn` is the Fréchet–Riesz map**, so the surface's vector-to-functional translation and the
one the backbone's gradient results are stated against are the same map. -/
theorem linFn_eq_toDual (b : Rn n) : linFn b = InnerProductSpace.toDual ℝ (Rn n) b :=
  (toDual_eq_innerSL b).symm

/-- The Riesz representative of `v` evaluated at `x` is the book's `⟨x, v⟩`. Every backbone result
about `HasGradientAtFn` produces the left-hand side, and every surface statement wants the right. -/
theorem toDual_apply_eq_pairing (v x : Rn n) :
    (InnerProductSpace.toDual ℝ (Rn n) v) x = pairing n x v :=
  toDual_apply_eq_innerL v x

end LinFn

/-! ### The canonical adjoint

Between arbitrarily paired spaces a transpose need not exist, so the backbone keeps the adjoint as
data. On `ℝⁿ` it is canonical, and `isAdjointPair_adjoint` already covers `innerₗ (Rn n)`: a
surface section writes `A*` as `LinearMap.adjoint A` and discharges the hypothesis with it. -/

end Rockafellar
