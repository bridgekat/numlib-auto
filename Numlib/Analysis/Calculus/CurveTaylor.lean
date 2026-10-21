import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Data.Finset.Pi

/-!
# Coefficients of Taylor models along polynomial curves

Positive compositions index the mixed derivative terms in the scalar coefficient of a
polynomial curve. These coefficients define the successive necessary sign tests, keeping
mixed derivative orders visible instead of testing only straight directions.
-/

noncomputable section
open scoped Nat
namespace CurveTaylor

/-- Ordered positive compositions of `j` into `k` parts. -/
def compositionIndices (j k : ℕ) : Finset (Fin k → Fin (j + 1)) :=
  Finset.univ.filter fun l => (∀ i, 1 ≤ (l i).val) ∧ ∑ i, (l i).val = j

/-- Membership records exactly positivity and the sum of the parts. -/
@[simp] theorem mem_compositionIndices {j k : ℕ} {l : Fin k → Fin (j + 1)} :
    l ∈ compositionIndices j k ↔ (∀ i, 1 ≤ (l i).val) ∧ ∑ i, (l i).val = j := by
  simp [compositionIndices]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar Taylor coefficient along an indexed polynomial curve, with no zeroth term. -/
def coefficient (f : E → ℝ) (x : E) (j : ℕ) (s : ℕ → E) : ℝ :=
  ∑ k ∈ Finset.Icc 1 j, ((k ! : ℝ)⁻¹) *
    ∑ l ∈ compositionIndices j k, iteratedFDeriv ℝ k f x (fun i => s (l i))

/-- There is no constant displacement coefficient. -/
@[simp] theorem coefficient_zero (f : E → ℝ) (x : E) (s : ℕ → E) :
    coefficient f x 0 s = 0 := by simp [coefficient]

/-- A coefficient depends only on the active curve jet up to that degree. -/
theorem coefficient_congr_jet (f : E → ℝ) (x : E) (j : ℕ) {s t : ℕ → E}
    (h : ∀ i, 1 ≤ i → i ≤ j → s i = t i) : coefficient f x j s = coefficient f x j t := by
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  funext i
  exact h _ ((mem_compositionIndices.mp hl).1 i) (by omega)

/-- All active orders satisfy their sign test whenever preceding coefficients vanish. -/
def IsOrderMinimizer (f : E → ℝ) (x : E) (q : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ q → ∀ s : ℕ → E,
    (∀ i, 1 ≤ i → i < j → coefficient f x i s = 0) → 0 ≤ coefficient f x j s

/-- Restricting the requested order preserves the curve conditions. -/
theorem IsOrderMinimizer.mono {f : E → ℝ} {x : E} {q r : ℕ}
    (h : IsOrderMinimizer f x q) (hr : r ≤ q) : IsOrderMinimizer f x r :=
  fun j hj hjr s hs => h j hj (hjr.trans hr) s hs

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem map_fin_vecCons {j n : ℕ} (s : ℕ → E) (a : Fin (j + 1))
    (v : Fin n → Fin (j + 1)) :
    (fun i => s (((Matrix.vecCons a v : Fin (n + 1) → Fin (j + 1)) i).val)) =
      Matrix.vecCons (s a.val) (fun i => s (v i).val) := by
  exact Fin.comp_cons (fun z : Fin (j + 1) => s z.val) a v

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem map_fin_vecEmpty {j : ℕ} (s : ℕ → E) :
    (fun i => s ((Matrix.vecEmpty : Fin 0 → Fin (j + 1)) i)) = Matrix.vecEmpty := by
  funext i
  exact i.elim0

/-- The degree-1 curve coefficient, with all ordered mixed terms visible. -/
theorem coefficient_one (f : E → ℝ) (x : E) (s : ℕ → E) :
    coefficient f x 1 s =
      fderiv ℝ f x (s 1) := by
  have hI : Finset.Icc 1 1 = {1} := by decide
  have h1 : compositionIndices 1 1 = {![1]} := by decide
  norm_num [coefficient, hI, h1]

/-- The degree-2 curve coefficient, with all ordered mixed terms visible. -/
theorem coefficient_two (f : E → ℝ) (x : E) (s : ℕ → E) :
    coefficient f x 2 s =
      fderiv ℝ f x (s 2) +
      (iteratedFDeriv ℝ 2 f x ![s 1, s 1]) / 2 := by
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  have h1 : compositionIndices 2 1 = {![2]} := by decide
  have h2 : compositionIndices 2 2 = {![1, 1]} := by decide
  norm_num [coefficient, hI, h1, h2]
  simp only [map_fin_vecCons, map_fin_vecEmpty]
  norm_num
  ring

/-- The degree-3 curve coefficient, with all ordered mixed terms visible. -/
theorem coefficient_three (f : E → ℝ) (x : E) (s : ℕ → E) :
    coefficient f x 3 s =
      fderiv ℝ f x (s 3) +
      (iteratedFDeriv ℝ 2 f x ![s 1, s 2] +
        iteratedFDeriv ℝ 2 f x ![s 2, s 1]) / 2 +
      (iteratedFDeriv ℝ 3 f x ![s 1, s 1, s 1]) / 6 := by
  have hI : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have h1 : compositionIndices 3 1 = {![3]} := by decide
  have h2 : compositionIndices 3 2 = {![1, 2], ![2, 1]} := by decide
  have h3 : compositionIndices 3 3 = {![1, 1, 1]} := by decide
  norm_num [coefficient, hI, h1, h2, h3]
  simp only [map_fin_vecCons, map_fin_vecEmpty]
  norm_num
  ring

set_option maxRecDepth 4096 in
/-- The degree-4 curve coefficient, with all ordered mixed terms visible. -/
theorem coefficient_four (f : E → ℝ) (x : E) (s : ℕ → E) :
    coefficient f x 4 s =
      fderiv ℝ f x (s 4) +
      (iteratedFDeriv ℝ 2 f x ![s 1, s 3] +
        iteratedFDeriv ℝ 2 f x ![s 2, s 2] +
        iteratedFDeriv ℝ 2 f x ![s 3, s 1]) / 2 +
      (iteratedFDeriv ℝ 3 f x ![s 1, s 1, s 2] +
        iteratedFDeriv ℝ 3 f x ![s 1, s 2, s 1] +
        iteratedFDeriv ℝ 3 f x ![s 2, s 1, s 1]) / 6 +
      (iteratedFDeriv ℝ 4 f x ![s 1, s 1, s 1, s 1]) / 24 := by
  have hI : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have h1 : compositionIndices 4 1 = {![4]} := by decide
  have h2 : compositionIndices 4 2 = {![1, 3], ![2, 2], ![3, 1]} := by decide
  have h3 : compositionIndices 4 3 = {![1, 1, 2], ![1, 2, 1], ![2, 1, 1]} := by decide
  have h4 : compositionIndices 4 4 = {![1, 1, 1, 1]} := by decide
  norm_num [coefficient, hI, h1, h2, h3, h4]
  simp only [map_fin_vecCons, map_fin_vecEmpty]
  norm_num
  ring

end CurveTaylor
