import Numlib.Optimization.LowerBounds.ZeroChain

/-!
# Zero-chain lower bounds

Section 4.2 defines deterministic methods through histories of actual objective and derivative
values. Zero-respecting methods preserve a coordinate only when all derivative tensors in that
history vanish in that coordinate. The zero-chain property then limits support growth to one
coordinate per iteration.

Finite dimensions are retained in each objective, and methods operate in every finite dimension.
Hitting times and best worst-case complexity take values in `ℕ∞`, so a method which never
terminates has infinite hitting time. The source complexity definition is equation (4.2.2);
its references to (4.2.3) in Lemma 4.2.3 are numbering slips.
-/

namespace CartisGouldToint

/-- A `p`th-order zero-chain objective, using actual iterated Fréchet derivatives in every slot. -/
def zeroChain {n : ℕ} (p : ℕ) (f : ZeroChain.Space n → ℝ) : Prop :=
  ZeroChain.IsZeroChain p f

/-- A deterministic oracle method: its next point depends only on a finite history of oracle
evaluations, and its actual execution starts at zero in every finite dimension. -/
abbrev oracleMethodClass (p : ℕ) := ZeroChain.OracleMethod p

/-- The zero-respecting subclass of deterministic oracle methods, as in (4.2.1). -/
def zeroRespectingMethodClass (p : ℕ) : Set (oracleMethodClass p) :=
  {M | ZeroChain.IsZeroRespectingMethod M}

/-- The class `F(Δ,p)` with a fixed common Lipschitz bound `L` on the `p`th derivative. -/
def zeroChainFunctionClass (p : ℕ) (Δ L : ℝ) : Set ZeroChain.Problem :=
  ZeroChain.functionClass p Δ L

/-- The first index at which the actual gradient norm is at most ε, or infinity if none exists. -/
noncomputable def oracleHittingTime {n p : ℕ} (M : oracleMethodClass p)
    (f : ZeroChain.Space n → ℝ) (ε : ℝ) : ℕ∞ :=
  ZeroChain.hittingTime f (M.iterates f) ε

/-- Best worst-case complexity: infimum over methods, followed by supremum over objectives,
as in equation (4.2.2). The objective class may contain different finite dimensions. -/
noncomputable def oracleClassComplexity (p : ℕ) (C : Set (oracleMethodClass p))
    (F : Set ZeroChain.Problem) (ε : ℝ) : ℕ∞ :=
  ZeroChain.methodClassComplexity p C F ε

/-- Lemma 4.2.1: rescaling the value and the variables preserves a zero chain. The variable
quotient `x/μ₂` is scalar multiplication by `μ₂⁻¹`. The proof uses the iterated chain rule. -/
theorem lemma_4_2_1 {n p : ℕ} {f : ZeroChain.Space n → ℝ}
    (hf : zeroChain p f) (μ₁ μ₂ : ℝ) (_hμ₂ : μ₂ ≠ 0) :
    zeroChain p (fun x => μ₁ * f (μ₂⁻¹ • x)) := hf.scale μ₁ μ₂⁻¹

/-- Lemma 4.2.2: after `k` iterations, a zero-respecting method applied to a zero chain has
zero coordinates in positions `k+1,...,n` in the source's one-based indexing. The derivative
history property of the method, rather than this support conclusion, is assumed. -/
theorem lemma_4_2_2 {n p : ℕ} {Δ L : ℝ} {f : ZeroChain.Space n → ℝ}
    (_hp : 1 ≤ p) (_hclass : (⟨n, f⟩ : ZeroChain.Problem) ∈ zeroChainFunctionClass p Δ L)
    (hf : zeroChain p f) (M : oracleMethodClass p) (hM : M ∈ zeroRespectingMethodClass p) :
    ∀ k ≤ n - 1, ∀ j : Fin n, k ≤ j.val → M.iterates f k j = 0 := by
  intro k _ j hj
  exact ZeroChain.support_iterate hf (hM n f) k j hj

/-- Lemma 4.2.3: if a zero chain has gradient norm greater than ε on the hyperplane where its
last coordinate is zero, every zero-respecting method needs at least its dimension-many
iterations. Taking the infimum over methods preserves this bound, and adding objectives can
only increase the best worst-case complexity. Dimension `n+1` makes the nonempty last
coordinate explicit. Both displayed inequalities in the source are retained. -/
theorem lemma_4_2_3 {n p : ℕ} {Δ L ε : ℝ} {f : ZeroChain.Space (n + 1) → ℝ}
    (_hp : 1 ≤ p) (_hε : 0 < ε)
    (hclass : (⟨n + 1, f⟩ : ZeroChain.Problem) ∈ zeroChainFunctionClass p Δ L)
    (hf : zeroChain p f)
    (hhard : ∀ x : ZeroChain.Space (n + 1), x (Fin.last n) = 0 → ε < ‖gradient f x‖) :
    oracleClassComplexity p (zeroRespectingMethodClass p) {⟨n + 1, f⟩} ε ≤
        oracleClassComplexity p (zeroRespectingMethodClass p) (zeroChainFunctionClass p Δ L) ε ∧
      ((n + 1 : ℕ) : ℕ∞) ≤
        oracleClassComplexity p (zeroRespectingMethodClass p) {⟨n + 1, f⟩} ε := by
  constructor
  · exact ZeroChain.classComplexity_mono (Set.singleton_subset_iff.mpr hclass)
  · exact ZeroChain.dimension_le_singleton_complexity hf hhard

end CartisGouldToint
