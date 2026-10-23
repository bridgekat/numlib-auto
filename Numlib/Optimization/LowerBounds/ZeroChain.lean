import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic

/-!
# Zero-chain objectives and zero-respecting methods

A derivative coordinate vanishes when the actual iterated Fréchet derivative is zero whenever
one input is the corresponding coordinate vector. A zero-chain objective reveals at most one
new coordinate beyond the support of a point. A zero-respecting sequence preserves a coordinate
which has vanished in every derivative in its full oracle history.

Coordinates use `Fin n`: the source tail `x_j = ... = x_n = 0` starts at zero-based index `j-1`.
-/

open scoped ContDiff

namespace ZeroChain

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The order-`q` derivative vanishes in coordinate `j`, in every tensor slot. -/
def DerivativeCoordinateZero {n : ℕ} (f : Space n → ℝ) (q : ℕ) (x : Space n)
    (j : Fin n) : Prop :=
  ∀ (v : Fin q → Space n) (a : Fin q), v a = EuclideanSpace.single j 1 →
    iteratedFDeriv ℝ q f x v = 0

/-- A `p`th-order zero chain is `C^p` and reveals at most the coordinate immediately after
an initial coordinate segment. All tensors are the actual derivatives of `f`. -/
structure IsZeroChain {n : ℕ} (p : ℕ) (f : Space n → ℝ) : Prop where
  smooth : ContDiff ℝ p f
  tail : ∀ (x : Space n) (r : ℕ), (∀ j : Fin n, r ≤ j.val → x j = 0) →
    ∀ j : Fin n, r < j.val → ∀ q : ℕ, 1 ≤ q → q ≤ p → DerivativeCoordinateZero f q x j

/-- A sequence respects zero coordinates of every derivative observed so far. The history
condition uses all earlier points, all permitted derivative orders, and all tensor slots.
The initialization is zero; no bound on the support of subsequent iterates is assumed. -/
structure IsZeroRespectingSequence {n : ℕ} (p : ℕ) (f : Space n → ℝ)
    (x : ℕ → Space n) : Prop where
  initial : x 0 = 0
  history : ∀ k (j : Fin n),
    (∀ i ≤ k, ∀ q : ℕ, 1 ≤ q → q ≤ p → DerivativeCoordinateZero f q (x i) j) →
    x (k + 1) j = 0

/-- Constant scaling of the objective and variables preserves the zero-chain property.
The derivative identity follows from the iterated chain rule for constant scalar multiplication. -/
theorem IsZeroChain.scale {n p : ℕ} {f : Space n → ℝ} (hf : IsZeroChain p f)
    (b a : ℝ) : IsZeroChain p (fun x => b * f (a • x)) := by
  have hg : ContDiff ℝ p (fun x : Space n => f (a • x)) :=
    hf.smooth.comp (contDiff_id.const_smul a)
  refine ⟨by simpa only [smul_eq_mul] using hg.const_smul b, ?_⟩
  intro x r hx j hj q hq hqp v z hz
  have htail : ∀ l : Fin n, r ≤ l.val → (a • x) l = 0 := by
    intro l hl
    simp [hx l hl]
  have hzero := hf.tail (a • x) r htail j hj q hq hqp v z hz
  have hfq : ContDiff ℝ q f := hf.smooth.of_le (by exact_mod_cast hqp)
  have hgq : ContDiffAt ℝ q (fun x : Space n => f (a • x)) x :=
    (hg.of_le (by exact_mod_cast hqp)).contDiffAt
  change iteratedFDeriv ℝ q (fun x : Space n => b • f (a • x)) x v = 0
  rw [iteratedFDeriv_const_smul_apply' hgq,
    congrFun (iteratedFDeriv_comp_const_smul a hfq) x]
  simp only [smul_apply, smul_eq_mul, hzero, mul_zero]

/-- By iteration `k`, a zero-respecting method on a zero chain can have explored only the first
`k` coordinates. This is derived from the full derivative history, rather than imposed on a run. -/
theorem support_iterate {n p : ℕ} {f : Space n → ℝ} (hf : IsZeroChain p f)
    {x : ℕ → Space n} (hx : IsZeroRespectingSequence p f x) :
    ∀ k (j : Fin n), k ≤ j.val → x k j = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      intro j _
      rw [hx.initial]
      rfl
    | succ k =>
      intro j hj
      apply hx.history k j
      intro i hi q hq hqp
      exact hf.tail (x i) i (fun l hl => ih i (by omega) l hl) j (by omega) q hq hqp

/-- A single oracle evaluation records the point, objective value, and every allowed derivative
order. Derivative order `q.val+1` ranges from one through `p`. -/
structure OracleEvaluation (n p : ℕ) where
  point : Space n
  value : ℝ
  derivative : (q : Fin p) → Space n [×(q.val + 1)]→L[ℝ] ℝ

/-- Evaluate the objective and its actual derivative tensors at a point. -/
noncomputable def oracleAt {n p : ℕ} (f : Space n → ℝ) (x : Space n) : OracleEvaluation n p :=
  ⟨x, f x, fun q => iteratedFDeriv ℝ (q.val + 1) f x⟩

/-- A deterministic method chooses its next point from the finite history of oracle data.
It is defined in every finite dimension, as required for dimension-varying problem classes. -/
structure OracleMethod (p : ℕ) where
  next : (n k : ℕ) → (Fin (k + 1) → OracleEvaluation n p) → Space n

/-- The actual execution of an oracle method, initialized at zero. The recursive calls only
refer to already computed iterates; the method never receives `f` itself. -/
noncomputable def OracleMethod.iterates {p n : ℕ} (M : OracleMethod p)
    (f : Space n → ℝ) : ℕ → Space n
  | 0 => 0
  | k + 1 => M.next n k (fun i => oracleAt f (M.iterates f i.val))
termination_by k => k

/-- The execution of every method starts at the zero point. -/
@[simp] theorem OracleMethod.iterates_zero {p n : ℕ} (M : OracleMethod p)
    (f : Space n → ℝ) : M.iterates f 0 = 0 := by
  rw [OracleMethod.iterates]

/-- Each next iterate is determined by the actual finite oracle history. -/
theorem OracleMethod.iterates_succ {p n : ℕ} (M : OracleMethod p)
    (f : Space n → ℝ) (k : ℕ) :
    M.iterates f (k + 1) = M.next n k (fun i => oracleAt f (M.iterates f i.val)) := by
  rw [OracleMethod.iterates]

/-- A method is zero respecting when its actual execution respects its full derivative history
for every objective in every finite dimension. -/
def IsZeroRespectingMethod {p : ℕ} (M : OracleMethod p) : Prop :=
  ∀ (n : ℕ) (f : Space n → ℝ), IsZeroRespectingSequence p f (M.iterates f)

/-- A method which always chooses zero. It witnesses nonemptiness of the method class. -/
def zeroMethod (p : ℕ) : OracleMethod p := ⟨fun _ _ _ => 0⟩

/-- The stationary zero method respects every derivative history. -/
theorem zeroMethod_isZeroRespecting (p : ℕ) : IsZeroRespectingMethod (zeroMethod p) := by
  intro n f
  refine ⟨by simp, ?_⟩
  intro k j _
  simp [OracleMethod.iterates_succ, zeroMethod]

/-- The zero-respecting class is inhabited, so its minimax lower bounds do not rely on an empty
infimum over methods. -/
instance zeroRespectingMethod_nonempty (p : ℕ) :
    Nonempty {M : OracleMethod p // IsZeroRespectingMethod M} :=
  ⟨⟨zeroMethod p, zeroMethod_isZeroRespecting p⟩⟩

/-- A finite-dimensional real objective, retaining the dimension as part of the problem. -/
structure Problem where
  dimension : ℕ
  objective : Space dimension → ℝ

/-- First gradient-tolerance hitting time, with infinity when the method never hits the test. -/
noncomputable def hittingTime {n : ℕ} (f : Space n → ℝ) (x : ℕ → Space n) (ε : ℝ) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | ‖gradient f (x k)‖ ≤ ε})

/-- A natural lower bound on hitting time is equivalent to exclusion of every earlier hit. -/
theorem natCast_le_hittingTime_iff {n : ℕ} (f : Space n → ℝ) (x : ℕ → Space n)
    (ε : ℝ) (N : ℕ) :
    (N : ℕ∞) ≤ hittingTime f x ε ↔ ∀ k, ‖gradient f (x k)‖ ≤ ε → N ≤ k := by
  constructor
  · intro h k hk
    exact ENat.natCast_le_natCast.mp (h.trans (sInf_le ⟨k, hk, rfl⟩))
  · intro h
    apply le_sInf
    rintro b ⟨k, hk, rfl⟩
    exact ENat.natCast_le_natCast.mpr (h k hk)

/-- The source function class: smooth objectives in varying finite dimensions, with a common
`p`th derivative Lipschitz constant, a finite lower bound, and initial objective gap at most Δ. -/
def functionClass (p : ℕ) (Δ L : ℝ) : Set Problem :=
  {P | ContDiff ℝ ∞ P.objective ∧ BddBelow (Set.range P.objective) ∧
    P.objective 0 - sInf (Set.range P.objective) ≤ Δ ∧
    ∀ x y, ‖iteratedFDeriv ℝ p P.objective x - iteratedFDeriv ℝ p P.objective y‖ ≤
      L * ‖x - y‖}

/-- Best worst-case hitting time for a chosen deterministic method class and objective class.
The infimum over methods is outside the supremum over objectives. -/
noncomputable def methodClassComplexity (p : ℕ) (C : Set (OracleMethod p))
    (F : Set Problem) (ε : ℝ) : ℕ∞ :=
  ⨅ M : C, ⨆ P : F, hittingTime P.val.objective (M.val.iterates P.val.objective) ε

/-- Best worst-case hitting time specialized to zero-respecting methods. -/
noncomputable def classComplexity (p : ℕ) (F : Set Problem) (ε : ℝ) : ℕ∞ :=
  methodClassComplexity p {M | IsZeroRespectingMethod M} F ε

/-- Enlarging the objective class can only increase best worst-case complexity. -/
theorem classComplexity_mono {p : ℕ} {F G : Set Problem} {ε : ℝ} (hFG : F ⊆ G) :
    classComplexity p F ε ≤ classComplexity p G ε := by
  apply iInf_mono
  intro M
  apply iSup_mono'
  intro P
  exact ⟨⟨P.val, hFG P.property⟩, le_rfl⟩

/-- If the gradient remains above ε whenever the last coordinate is zero, a zero-respecting
execution cannot hit ε before its dimension-many iterations. -/
theorem dimension_le_hittingTime {n p : ℕ} {f : Space (n + 1) → ℝ}
    (hf : IsZeroChain p f) {x : ℕ → Space (n + 1)} (hx : IsZeroRespectingSequence p f x)
    {ε : ℝ} (hhard : ∀ z : Space (n + 1), z (Fin.last n) = 0 → ε < ‖gradient f z‖) :
    ((n + 1 : ℕ) : ℕ∞) ≤ hittingTime f x ε := by
  apply (natCast_le_hittingTime_iff f x ε (n + 1)).mpr
  intro k hk
  by_contra hkn
  have hz := support_iterate hf hx k (Fin.last n) (by simpa only [Fin.val_last] using Nat.le_of_lt_succ (Nat.lt_of_not_ge hkn))
  exact (not_le_of_gt (hhard (x k) hz)) hk

/-- A single difficult zero chain gives a lower bound on the entire method class. -/
theorem dimension_le_singleton_complexity {n p : ℕ} {f : Space (n + 1) → ℝ}
    (hf : IsZeroChain p f) {ε : ℝ}
    (hhard : ∀ z : Space (n + 1), z (Fin.last n) = 0 → ε < ‖gradient f z‖) :
    ((n + 1 : ℕ) : ℕ∞) ≤ classComplexity p {⟨n + 1, f⟩} ε := by
  apply le_iInf
  intro M
  exact (dimension_le_hittingTime hf (M.property _ f) hhard).trans
    (le_iSup_of_le ⟨⟨n + 1, f⟩, Set.mem_singleton _⟩ le_rfl)

end ZeroChain
