import Numlib.Optimization.ZeroChains
import Numlib.Analysis.Normed.Multilinear.Diagonal

/-!
# Deterministic derivative-oracle methods

A method receives only the finite history of actual objective values and derivatives of
orders one through `p`. It specifies a rule in every finite dimension, so worst-case function
classes can range over dimensions. Stationary attainment has values in `ℕ∞`, with infinity
for a trace that never attains the requested gradient tolerance. Minimax complexity is the
infimum over methods of the supremum over functions, with no complexity certificate in the
method interface.
-/

noncomputable section
open scoped ContDiff ENNReal

namespace Optimization.DerivativeOracle
open ZeroChains

/-- The complete order-`p` oracle response at one query. -/
structure Reply (n p : ℕ) where
  value : ℝ
  derivative : ∀ q : Fin p,
    ContinuousMultilinearMap ℝ (fun _ : Fin (q.val + 1) => Space n) ℝ

/-- The oracle returns the actual value and actual iterated Fréchet derivatives. -/
def oracle {n : ℕ} (p : ℕ) (f : Space n → ℝ) (x : Space n) : Reply n p where
  value := f x
  derivative q := iteratedFDeriv ℝ (q.val + 1) f x

/-- The value component of an oracle response is the queried objective value. -/
@[simp] theorem oracle_value {n p : ℕ} (f : Space n → ℝ) (x : Space n) :
    (oracle p f x).value = f x := rfl

/-- Every derivative component is an actual derivative, including mixed evaluations. -/
@[simp] theorem oracle_derivative {n p : ℕ} (f : Space n → ℝ) (x : Space n) (q : Fin p) :
    (oracle p f x).derivative q = iteratedFDeriv ℝ (q.val + 1) f x := rfl

/-- A deterministic order-`p` method is a family of finite oracle-history rules.
The rule has no access to the objective except through the supplied responses. -/
structure Method (p : ℕ) where
  next : ∀ n k : ℕ, (Fin (k + 1) → Reply n p) → Space n

/-- The actual trace generated recursively from zero and the full previous oracle history. -/
noncomputable def Method.iterate {p n : ℕ} (M : Method p) (f : Space n → ℝ) :
    (k : ℕ) → Space n
  | 0 => 0
  | k + 1 => M.next n k (fun i => oracle p f (M.iterate f i.val))
termination_by k => k

/-- All methods start at zero. -/
@[simp] theorem Method.iterate_zero {p n : ℕ} (M : Method p) (f : Space n → ℝ) :
    M.iterate f 0 = 0 := by rw [Method.iterate]

/-- The next iterate is the method's rule applied to exactly the previous oracle responses. -/
theorem Method.iterate_succ {p n : ℕ} (M : Method p) (f : Space n → ℝ) (k : ℕ) :
    M.iterate f (k + 1) = M.next n k (fun i => oracle p f (M.iterate f i.val)) := by
  rw [Method.iterate]

/-- Equal finite histories of actual responses force equal next queries. -/
theorem Method.iterate_succ_eq_of_oracle_eq {p n : ℕ} (M : Method p)
    (f g : Space n → ℝ) (k : ℕ)
    (h : ∀ j ≤ k, oracle p f (M.iterate f j) = oracle p g (M.iterate g j)) :
    M.iterate f (k + 1) = M.iterate g (k + 1) := by
  rw [M.iterate_succ, M.iterate_succ]
  congr 1
  funext i
  exact h i.val (Nat.le_of_lt_succ i.isLt)

/-- The method that always queries the origin. It witnesses nonemptiness of the method class. -/
def zeroMethod (p : ℕ) : Method p := ⟨fun _ _ _ => 0⟩

/-- The origin-querying method's actual trace is constantly zero. -/
@[simp] theorem zeroMethod_iterate {p n : ℕ} (f : Space n → ℝ) (k : ℕ) :
    (zeroMethod p).iterate f k = 0 := by
  cases k with
  | zero => rw [Method.iterate]
  | succ k => rw [Method.iterate]; rfl

/-- A dimension-polymorphic method is zero respecting on every objective. -/
def Method.IsZeroRespecting {p : ℕ} (M : Method p) : Prop :=
  ∀ n (f : Space n → ℝ), ZeroChains.IsZeroRespecting p f (M.iterate f)

/-- The class of all zero-respecting order-`p` deterministic oracle methods. -/
def zeroRespectingMethods (p : ℕ) : Set (Method p) := {M | M.IsZeroRespecting}

/-- Membership means that the actual recursively generated trace obeys the support rule. -/
@[simp] theorem mem_zeroRespectingMethods {p : ℕ} (M : Method p) :
    M ∈ zeroRespectingMethods p ↔ M.IsZeroRespecting := Iff.rfl

/-- The origin-querying method is zero respecting, so this subclass is nonempty. -/
theorem zeroMethod_mem_zeroRespectingMethods (p : ℕ) :
    zeroMethod p ∈ zeroRespectingMethods p := by
  intro n f
  refine ⟨by simp, ?_⟩
  intro k
  simp

/-- Smooth functions with a bounded initial objective gap and a prescribed highest-derivative
Lipschitz bound. The diagonal norm is the homogeneous tensor norm; dimensions are not fixed. -/
structure FunctionClass (p : ℕ) (Δ L : ℝ) (n : ℕ) (f : Space n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  bounded_below : BddBelow (Set.range f)
  initial_gap : f 0 - sInf (Set.range f) ≤ Δ
  lipschitz_nonneg : 0 ≤ L
  lipschitz : ∀ x y,
    (iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y).diagonalNorm ≤ L * ‖x - y‖

/-- A finite-dimensional scalar objective together with its dimension. -/
abbrev Objective := Σ n : ℕ, Space n → ℝ

/-- The function class as a single set, permitting dimension growth with the tolerance. -/
def functionClass (p : ℕ) (Δ L : ℝ) : Set Objective :=
  {f | FunctionClass p Δ L f.1 f.2}

/-- Class membership retains the actual smoothness, gap, and derivative bound. -/
@[simp] theorem mem_functionClass {p n : ℕ} (Δ L : ℝ) (f : Space n → ℝ) :
    (⟨n, f⟩ : Objective) ∈ functionClass p Δ L ↔ FunctionClass p Δ L n f := Iff.rfl

/-- First gradient-tolerance attainment, with infinity if there is no attaining iterate. -/
def firstStationaryTime {n : ℕ} (f : Space n → ℝ) (x : ℕ → Space n) (ε : ℝ) : ℕ∞ :=
  ⨅ k : {k : ℕ // ‖gradient f (x k)‖ ≤ ε}, (k.val : ℕ∞)

/-- Nonattainment is represented by infinity. -/
theorem firstStationaryTime_eq_top_iff {n : ℕ} (f : Space n → ℝ)
    (x : ℕ → Space n) (ε : ℝ) :
    firstStationaryTime f x ε = ⊤ ↔ ∀ k, ε < ‖gradient f (x k)‖ := by
  simp [firstStationaryTime]

/-- A lower bound on first attainment follows exactly from failure at every earlier index. -/
theorem le_firstStationaryTime_iff {n N : ℕ} (f : Space n → ℝ)
    (x : ℕ → Space n) (ε : ℝ) :
    (N : ℕ∞) ≤ firstStationaryTime f x ε ↔ ∀ k < N, ε < ‖gradient f (x k)‖ := by
  simp only [firstStationaryTime, le_iInf_iff, ENat.natCast_le_natCast, Subtype.forall]
  constructor
  · intro h k hk
    by_contra hnot
    have := h k (le_of_not_gt hnot)
    omega
  · intro h k hk
    by_contra hnot
    have := h k (Nat.lt_of_not_ge hnot)
    exact (not_lt_of_ge hk) this

/-- A finite first attainment is precisely a successful query preceded by unsuccessful ones. -/
theorem firstStationaryTime_eq_natCast_iff {n N : ℕ} (f : Space n → ℝ)
    (x : ℕ → Space n) (ε : ℝ) :
    firstStationaryTime f x ε = N ↔ ‖gradient f (x N)‖ ≤ ε ∧
      ∀ k < N, ε < ‖gradient f (x k)‖ := by
  rw [firstStationaryTime, ENat.iInf_eq_natCast_iff]
  simp only [ENat.natCast_inj, Subtype.exists, exists_prop, exists_eq_right,
    Subtype.forall, ENat.natCast_le_natCast]
  constructor
  · rintro ⟨hN, h⟩
    exact ⟨hN, (le_firstStationaryTime_iff f x ε).mp
      ((le_iInf_iff).mpr (by simpa only [ENat.natCast_le_natCast, Subtype.forall] using h))⟩
  · rintro ⟨hN, h⟩
    exact ⟨hN, by
      simpa only [ENat.natCast_le_natCast, Subtype.forall] using
        (le_iInf_iff.mp ((le_firstStationaryTime_iff f x ε).mpr h))⟩

/-- Best worst-case iteration complexity, taking the infimum over permitted methods and
supremum over the dimension-varying objective class. -/
def minimax {p : ℕ} (methods : Set (Method p)) (functions : Set Objective) (ε : ℝ) : ℕ∞ :=
  ⨅ M : methods, ⨆ f : functions, firstStationaryTime f.val.2 (M.val.iterate f.val.2) ε

/-- Increasing the objective class can only increase best worst-case complexity. -/
theorem minimax_mono_functions {p : ℕ} (methods : Set (Method p))
    {functions₁ functions₂ : Set Objective} (h : functions₁ ⊆ functions₂) (ε : ℝ) :
    minimax methods functions₁ ε ≤ minimax methods functions₂ ε := by
  apply iInf_mono
  intro M
  apply iSup_le
  intro f
  exact le_iSup_of_le ⟨f.val, h f.property⟩ le_rfl

/-- A hidden final coordinate prevents every earlier iterate from meeting the tolerance. -/
theorem _root_.Optimization.ZeroChains.IsZeroChain.le_firstStationaryTime
    {p n : ℕ} {f : Space (n + 1) → ℝ}
    (hf : IsZeroChain p f) {x : ℕ → Space (n + 1)}
    (hx : ZeroChains.IsZeroRespecting p f x) {ε : ℝ}
    (hhidden : ∀ y : Space (n + 1),
      y (Fin.last n) = 0 → ε < ‖gradient f y‖) :
    (n + 1 : ℕ∞) ≤ firstStationaryTime f x ε := by
  apply (le_firstStationaryTime_iff f x ε).mpr
  intro k hk
  apply hhidden
  exact (coordinateSupport_subset_initial_iff (x k) k).mp (hf.support_iterate hx k)
    (Fin.last n) (by simpa using Nat.le_of_lt_succ hk)

/-- A hidden-coordinate zero chain gives a minimax lower bound for any class of methods
whose actual traces on this objective are zero respecting. -/
theorem _root_.Optimization.ZeroChains.IsZeroChain.le_minimax {p n : ℕ} {f : Space (n + 1) → ℝ}
    (hf : IsZeroChain p f) (methods : Set (Method p)) (functions : Set Objective)
    (hmem : (⟨n + 1, f⟩ : Objective) ∈ functions)
    (hmethods : ∀ M ∈ methods, ZeroChains.IsZeroRespecting p f (M.iterate f))
    {ε : ℝ}
    (hhidden : ∀ y : Space (n + 1),
      y (Fin.last n) = 0 → ε < ‖gradient f y‖) :
    (n + 1 : ℕ∞) ≤ minimax methods functions ε := by
  apply le_iInf
  intro M
  exact le_iSup_of_le ⟨⟨n + 1, f⟩, hmem⟩
    (hf.le_firstStationaryTime (hmethods M.val M.property) hhidden)

end Optimization.DerivativeOracle
