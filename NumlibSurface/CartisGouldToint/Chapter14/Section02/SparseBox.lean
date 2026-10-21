import Numlib.Optimization.SparseBoxLinearization
import NumlibSurface.CartisGouldToint.Chapter14.Section02

/-!
# Chapter 14, Section 2: the sparse box linear subproblem

Lemma 14.2.5 is an actual finite-dimensional global minimum. Its optional coordinates solve
the binary maximization (14.2.21), with the remaining budget as an inequality. The OCR's
"max" in (14.2.18)–(14.2.19) is corrected to "min", as required by (14.2.20) and its proof.
The result allows zero gradient coordinates and tied gains without asserting uniqueness.
-/

noncomputable section
open scoped BigOperators
open Set Optimization
namespace CartisGouldToint.Chapter14.Section02
variable {n : ℕ}

/-- The actual sparse box displacement (14.2.20), with mandatory and optional retained indices. -/
def sparseBoxStep (x g : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (J : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (SparseConstraints.boxLinearStep (fun i => x i) (fun i => g i) δ J)

/-- The coordinate formula selects scalar box minima and cancels every dropped coordinate. -/
@[simp] theorem sparseBoxStep_apply (x g : EuclideanSpace ℝ (Fin n)) (δ : ℝ)
    (J : Finset (Fin n)) (i : Fin n) :
    sparseBoxStep x g δ J i =
      if i ∈ mandatoryIndices x δ ∪ J then -δ * (SignType.sign (g i) : ℝ) else -x i := rfl

/-- The box bound and translated sparsity both hold for the explicit Euclidean displacement. -/
theorem sparseBoxStep_feasible {x g : EuclideanSpace ℝ (Fin n)} {δ : ℝ} {k : ℕ}
    {J : Finset (Fin n)} (hδ : 0 ≤ δ) (hx : x ∈ SparseFeasibleSet k)
    (hJ : J ∈ optionalSupports x δ k) :
    (∀ i, |sparseBoxStep x g δ J i| ≤ δ) ∧ x + sparseBoxStep x g δ J ∈ SparseFeasibleSet k := by
  exact SparseConstraints.boxLinearStep_mem_feasibleBoxSteps hδ hx hJ

/-- A maximum of the binary gain problem gives the actual Euclidean inner-product minimum. -/
theorem sparseBoxStep_isMinOn {x g : EuclideanSpace ℝ (Fin n)} {δ : ℝ} {k : ℕ}
    {J : Finset (Fin n)}
    (hJ : SparseConstraints.IsOptimalOptionalSupport (fun i => x i) (fun i => g i) δ k J) :
    IsMinOn (fun d => inner ℝ g d)
      {d : EuclideanSpace ℝ (Fin n) | (∀ i, |d i| ≤ δ) ∧ x + d ∈ SparseFeasibleSet k}
      (sparseBoxStep x g δ J) := by
  intro d hd
  have h := SparseConstraints.boxLinearStep_isMinOn hJ hd
  simpa [PiLp.inner_apply, mul_comm, sparseBoxStep] using h

/-- Lemma 14.2.5: the finite binary maximum produces the feasible step (14.2.20) and a
true global linear minimum. The binary vector has zeros on mandatory indices and at most
the remaining number of ones. No uniqueness is claimed at zero coordinates or tied gains. -/
theorem lemma_14_2_5 {x g : EuclideanSpace ℝ (Fin n)} {δ : ℝ} {k : ℕ}
    (hδ : 0 ≤ δ) (hx : x ∈ SparseFeasibleSet k) :
    ∃ J : Finset (Fin n), ∃ τ : Fin n → ℝ,
      J ∈ optionalSupports x δ k ∧ τ = SparseConstraints.supportIndicator J ∧
      SparseConstraints.IsBinaryOptionalSelection (fun i => x i) δ k τ ∧
      (∀ υ, SparseConstraints.IsBinaryOptionalSelection (fun i => x i) δ k υ →
        ∑ i, υ i * optionalWeight x g δ i ≤ ∑ i, τ i * optionalWeight x g δ i) ∧
      (∀ i, |sparseBoxStep x g δ J i| ≤ δ) ∧
      x + sparseBoxStep x g δ J ∈ SparseFeasibleSet k ∧
      IsMinOn (fun d => inner ℝ g d)
        {d : EuclideanSpace ℝ (Fin n) | (∀ i, |d i| ≤ δ) ∧ x + d ∈ SparseFeasibleSet k}
        (sparseBoxStep x g δ J) := by
  obtain ⟨J, hJ⟩ := SparseConstraints.exists_optimalOptionalSupport
    (fun i => x i) (fun i => g i) δ k
  refine ⟨J, SparseConstraints.supportIndicator J, hJ.mem, rfl,
    SparseConstraints.supportIndicator_isBinaryOptionalSelection hJ.mem, ?_, ?_, ?_,
    sparseBoxStep_isMinOn hJ⟩
  · intro υ hυ
    exact hJ.binary_maximal hυ
  · exact (sparseBoxStep_feasible hδ hx hJ.mem).1
  · exact (sparseBoxStep_feasible hδ hx hJ.mem).2

end CartisGouldToint.Chapter14.Section02
