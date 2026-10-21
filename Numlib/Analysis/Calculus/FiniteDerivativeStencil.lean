import Numlib.Optimization.InexactTaylorModels
import Mathlib.Data.List.FinRange

/-!
# Verified finite stencils for low-degree derivative oracles

A stencil reconstructs one derivative tensor from a fixed finite list of lower-degree
queries. Its coefficients and offsets depend on the mesh, and reconstruction accesses the
objective only through those queries. Polynomial reproduction records the cancellation
conditions. A verified scheme includes a proof of its uniform error contract; no existence
of such a scheme for arbitrary dimensions or orders is asserted by the interface.
-/

noncomputable section
namespace FiniteDerivativeStencil
open Optimization.InexactTaylorModels
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual continuous multilinear tensor space of derivative order `i`. -/
abbrev Tensor (i : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ

/-- A fixed finite linear derivative stencil. Degree zero means an objective-value query.
The finite number of samples can depend on dimension and derivative orders, but not on
the mesh or the requested accuracy. Offsets contract at a uniform linear mesh rate. -/
structure Stencil (o i : ℕ) where
  size : ℕ
  degree : Fin size → Fin (o + 1)
  offset : ℝ → Fin size → E
  weight : (h : ℝ) → (r : Fin size) → Tensor E (degree r).val →L[ℝ] Tensor E i
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  offset_le : ∀ h, 0 < h → h ≤ 1 → ∀ r, ‖offset h r‖ ≤ radius * h

variable {E}

/-- Reconstruction reads exactly the finite lower-degree replies selected by the stencil. -/
def Stencil.fromOracle {o i : ℕ} (S : Stencil E o i)
    (O : (x : E) → (j : Fin (o + 1)) → Tensor E j.val) (x : E) (h : ℝ) : Tensor E i :=
  ∑ r : Fin S.size, S.weight h r (O (x + S.offset h r) (S.degree r))

/-- The stencil applied to the actual derivatives available from the low-degree oracle. -/
def Stencil.estimate {o i : ℕ} (S : Stencil E o i) (f : E → ℝ) (x : E) (h : ℝ) :
    Tensor E i := S.fromOracle (fun y j => iteratedFDeriv ℝ j.val f y) x h

/-- Reconstruction depends only on the sampled replies, even for arbitrary oracle data. -/
theorem Stencil.fromOracle_eq_of_replies_eq {o i : ℕ} (S : Stencil E o i)
    (O P : (x : E) → (j : Fin (o + 1)) → Tensor E j.val) (x : E) (h : ℝ)
    (he : ∀ r, O (x + S.offset h r) (S.degree r) = P (x + S.offset h r) (S.degree r)) :
    S.fromOracle O x h = S.fromOracle P x h := by
  unfold fromOracle
  apply Finset.sum_congr rfl
  intro r _
  rw [he r]

/-- Polynomial reproduction states the exact cancellation conditions on actual Taylor
polynomials. It does not identify arbitrary nonsymmetric tensors with their polynomial jets. -/
def Stencil.PolynomialExact {o i : ℕ} (S : Stencil E o i) (p : ℕ) : Prop :=
  ∀ (c : ℝ) (A : (j : ℕ) → Tensor E j) (x : E) (h : ℝ), 0 < h → h ≤ 1 →
    S.estimate (polynomial c A p) x h =
      iteratedFDeriv ℝ i (polynomial c A p) x

/-- Exact reproduction through one polynomial degree also reproduces every lower degree.
Higher-degree coefficient slots are filled by actual zero multilinear maps. -/
theorem Stencil.PolynomialExact.mono {o i p q : ℕ} {S : Stencil E o i}
    (hS : S.PolynomialExact p) (hqp : q ≤ p) : S.PolynomialExact q := by
  intro c A x h hh hh1
  let B : (j : ℕ) → Tensor E j := fun j => if j ≤ q then A j else 0
  have hpoly : polynomial c B p = polynomial c A q := by
    funext s
    unfold polynomial
    congr 1
    calc
      ∑ j ∈ Finset.Icc 1 p, B j (fun _ => s) / (j.factorial : ℝ) =
          ∑ j ∈ Finset.Icc 1 q, B j (fun _ => s) / (j.factorial : ℝ) := by
        symm
        apply Finset.sum_subset
        · intro j hj
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
            (Finset.mem_Icc.mp hj).2.trans hqp⟩
        · intro j hj hjq
          have hj' : ¬j ≤ q := by
            intro hj'
            exact hjq (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, hj'⟩)
          simp [B, hj']
      _ = ∑ j ∈ Finset.Icc 1 q, A j (fun _ => s) / (j.factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [B, (Finset.mem_Icc.mp hj).2]
  simpa only [hpoly] using hS c B x h hh hh1

/-- The literal sample list exposes the queried points and their bounded oracle degrees. -/
def Stencil.queries {o i : ℕ} (S : Stencil E o i) (x : E) (h : ℝ) :
    List (E × Fin (o + 1)) :=
  (List.finRange S.size).map (fun r => (x + S.offset h r, S.degree r))

/-- The finite sample count is fixed before the mesh and the evaluation point. -/
@[simp] theorem Stencil.queries_length {o i : ℕ} (S : Stencil E o i) (x : E) (h : ℝ) :
    (S.queries x h).length = S.size := by simp [queries]

/-- Every stencil query lies within the contracting mesh radius of its base point. -/
theorem Stencil.query_dist_le {o i : ℕ} (S : Stencil E o i) (x : E)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (r : Fin S.size) :
    dist (x + S.offset h r) x ≤ S.radius * h := by
  simpa only [dist_eq_norm, add_sub_cancel_left] using S.offset_le h hh hh1 r

/-- Every sampled point approaches the base point as the positive mesh tends to zero,
uniformly across the finite stencil. This is an explicit epsilon-delta formulation. -/
theorem Stencil.queries_approach {o i : ℕ} (S : Stencil E o i) (x : E)
    {ε : ℝ} (hε : 0 < ε) : ∃ η : ℝ, 0 < η ∧ ∀ h, 0 < h → h < η →
      ∀ r : Fin S.size, dist (x + S.offset h r) x < ε := by
  have hR := S.radius_nonneg
  refine ⟨min 1 (ε / (S.radius + 1)), lt_min zero_lt_one (div_pos hε (by positivity)), ?_⟩
  intro h hh hη r
  have h1 := (lt_min_iff.mp hη).1
  have h2 := (lt_div_iff₀ (show 0 < S.radius + 1 by positivity)).mp (lt_min_iff.mp hη).2
  have hb := S.query_dist_le x hh h1.le r
  nlinarith

/-- A verified family of finite derivative stencils. The error estimate is a defining
mathematical obligation, proved for each instance, with constants fixed before all points
and meshes. Polynomial cancellation and contraction are retained explicitly. -/
structure VerifiedScheme (f : E → ℝ) (o p : ℕ) where
  order_le : o ≤ p
  stencil : (i : ℕ) → i ∈ Finset.Icc (o + 1) p → Stencil E o i
  multiplier : ℕ → ℝ
  multiplier_nonneg : ∀ i ∈ Finset.Icc (o + 1) p, 0 ≤ multiplier i
  polynomial_exact : ∀ i (hi : i ∈ Finset.Icc (o + 1) p), (stencil i hi).PolynomialExact p
  accuracy : ∀ i (hi : i ∈ Finset.Icc (o + 1) p) (x : E) (h : ℝ), 0 < h → h ≤ 1 →
    ‖(stencil i hi).estimate f x h - iteratedFDeriv ℝ i f x‖ ≤ multiplier i * h

variable {f : E → ℝ} {o p : ℕ}

/-- Restrict the maximum reconstructed order, keeping the available oracle order and
all retained stencils and error multipliers unchanged. Polynomial cancellation at the
smaller degree follows from the original cancellation at every higher degree. -/
def VerifiedScheme.restrictOrder (S : VerifiedScheme f o p) {q : ℕ}
    (hoq : o ≤ q) (hqp : q ≤ p) : VerifiedScheme f o q where
  order_le := hoq
  stencil i hi := S.stencil i
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hqp⟩)
  multiplier := S.multiplier
  multiplier_nonneg i hi := S.multiplier_nonneg i
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hqp⟩)
  polynomial_exact i hi := (S.polynomial_exact i
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
      (Finset.mem_Icc.mp hi).2.trans hqp⟩)).mono hqp
  accuracy i hi := S.accuracy i
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hqp⟩)

/-- Restriction uses the identical retained stencil, with only its order-membership proof
transported to the original index interval. In particular its geometry and samples agree. -/
@[simp] theorem VerifiedScheme.restrictOrder_stencil (S : VerifiedScheme f o p) {q : ℕ}
    (hoq : o ≤ q) (hqp : q ≤ p) (i : ℕ) (hi : i ∈ Finset.Icc (o + 1) q) :
    (S.restrictOrder hoq hqp).stencil i hi = S.stencil i
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
        (Finset.mem_Icc.mp hi).2.trans hqp⟩) := rfl

/-- The full multiplier family is preserved, independently of all meshes and points. -/
@[simp] theorem VerifiedScheme.restrictOrder_multiplier (S : VerifiedScheme f o p) {q : ℕ}
    (hoq : o ≤ q) (hqp : q ≤ p) :
    (S.restrictOrder hoq hqp).multiplier = S.multiplier := rfl

/-- Restricting to the original maximum order changes none of the verified scheme. -/
@[simp] theorem VerifiedScheme.restrictOrder_self (S : VerifiedScheme f o p) :
    S.restrictOrder S.order_le le_rfl = S := by
  cases S
  rfl

/-- Successive restrictions agree with direct restriction, including the actual stencils. -/
@[simp] theorem VerifiedScheme.restrictOrder_restrictOrder (S : VerifiedScheme f o p)
    {q r : ℕ} (hoq : o ≤ q) (hqp : q ≤ p) (hor : o ≤ r) (hrq : r ≤ q) :
    (S.restrictOrder hoq hqp).restrictOrder hor hrq = S.restrictOrder hor (hrq.trans hqp) := rfl

/-- A retained stencil still has its original, stronger polynomial cancellation contract. -/
theorem VerifiedScheme.restrictOrder_polynomialExact (S : VerifiedScheme f o p) {q : ℕ}
    (hoq : o ≤ q) (hqp : q ≤ p) (i : ℕ) (hi : i ∈ Finset.Icc (o + 1) q) :
    ((S.restrictOrder hoq hqp).stencil i hi).PolynomialExact p :=
  S.polynomial_exact i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
    (Finset.mem_Icc.mp hi).2.trans hqp⟩)

/-- The actual reconstructed high-order tensor converges to the true derivative as the
positive mesh tends to zero. The bound is uniform in the evaluation point; this states
convergence in an explicit epsilon-delta form without another consistency assumption. -/
theorem VerifiedScheme.estimate_approach (S : VerifiedScheme f o p)
    {i : ℕ} (hi : i ∈ Finset.Icc (o + 1) p) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ h, 0 < h → h < η →
      ‖(S.stencil i hi).estimate f x h - iteratedFDeriv ℝ i f x‖ < ε := by
  have hK := S.multiplier_nonneg i hi
  refine ⟨min 1 (ε / (S.multiplier i + 1)),
    lt_min zero_lt_one (div_pos hε (by positivity)), ?_⟩
  intro h hh hη
  have h1 := (lt_min_iff.mp hη).1
  have h2 := (lt_div_iff₀ (show 0 < S.multiplier i + 1 by positivity)).mp
    (lt_min_iff.mp hη).2
  have hb := S.accuracy i hi x h hh h1.le
  nlinarith

/-- Clipping a requested accuracy at one produces the mesh used by a verified stencil. -/
def requestedMesh (h : ℝ) : ℝ := min h 1

/-- Positive requests produce admissible positive meshes. -/
theorem requestedMesh_pos {h : ℝ} (hh : 0 < h) : 0 < requestedMesh h :=
  lt_min hh zero_lt_one

/-- The mesh is no larger than the requested accuracy. -/
theorem requestedMesh_le (h : ℝ) : requestedMesh h ≤ h := min_le_left _ _

/-- Every chosen mesh lies in the stencil's unit mesh range. -/
theorem requestedMesh_le_one (h : ℝ) : requestedMesh h ≤ 1 := min_le_right _ _

/-- Approximate tensors are reconstructed from the finite stencils; available orders
remain exact. Values beyond the requested maximum degree are unused zero tensors. -/
def VerifiedScheme.oracle (S : VerifiedScheme f o p) (x : E) (h : ℕ → ℝ)
    (i : ℕ) : Tensor E i :=
  if hi : i ≤ o then iteratedFDeriv ℝ i f x else
  if hp : i ≤ p then
    (S.stencil i (Finset.mem_Icc.mpr ⟨by omega, hp⟩)).estimate f x (requestedMesh (h i))
  else 0

/-- The supplied low-order derivatives are exactly the available oracle derivatives. -/
@[simp] theorem VerifiedScheme.oracle_low (S : VerifiedScheme f o p) (x : E)
    (h : ℕ → ℝ) {i : ℕ} (hi : i ≤ o) :
    S.oracle x h i = iteratedFDeriv ℝ i f x := by simp [oracle, hi]

/-- The high-order tensor is the explicit finite stencil reconstruction. -/
theorem VerifiedScheme.oracle_high (S : VerifiedScheme f o p) (x : E)
    (h : ℕ → ℝ) {i : ℕ} (hi : i ∈ Finset.Icc (o + 1) p) :
    S.oracle x h i = (S.stencil i hi).estimate f x (requestedMesh (h i)) := by
  simp only [oracle, dite_eq_right (show ¬i ≤ o by have := (Finset.mem_Icc.mp hi).1; omega),
    dite_eq_left (Finset.mem_Icc.mp hi).2]

/-- Exact orders have zero error multipliers; higher orders retain their verified fixed
constants. The resulting family is independent of evaluation points and all requests. -/
def VerifiedScheme.errorMultiplier (S : VerifiedScheme f o p) (i : ℕ) : ℝ :=
  if i ≤ o then 0 else S.multiplier i

/-- The restricted oracle agrees with the original at every retained order, including
order zero and directly available orders, for arbitrary requested accuracies. -/
@[simp] theorem VerifiedScheme.restrictOrder_oracle (S : VerifiedScheme f o p) {q : ℕ}
    (hoq : o ≤ q) (hqp : q ≤ p) (x : E) (h : ℕ → ℝ) {i : ℕ} (hi : i ≤ q) :
    (S.restrictOrder hoq hqp).oracle x h i = S.oracle x h i := by
  by_cases hlo : i ≤ o
  · simp only [oracle_low _ _ _ hlo]
  · have hiq : i ∈ Finset.Icc (o + 1) q := Finset.mem_Icc.mpr ⟨by omega, hi⟩
    rw [VerifiedScheme.oracle_high _ _ _ hiq,
      S.oracle_high x h (Finset.mem_Icc.mpr ⟨by omega, hi.trans hqp⟩),
      restrictOrder_stencil]

/-- Restriction preserves every error multiplier, even outside the retained active orders. -/
@[simp] theorem VerifiedScheme.restrictOrder_errorMultiplier (S : VerifiedScheme f o p)
    {q : ℕ} (hoq : o ≤ q) (hqp : q ≤ p) (i : ℕ) :
    (S.restrictOrder hoq hqp).errorMultiplier i = S.errorMultiplier i := rfl

/-- All active error multipliers are nonnegative. -/
theorem VerifiedScheme.errorMultiplier_nonneg (S : VerifiedScheme f o p)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 p) : 0 ≤ S.errorMultiplier i := by
  unfold errorMultiplier
  split_ifs with h
  · exact le_rfl
  · exact S.multiplier_nonneg i (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hi).2⟩)

/-- A verified finite scheme satisfies the actual implicit dynamic accuracy contract at
all points and every positive requested accuracy, including requests larger than one. -/
theorem VerifiedScheme.oracle_accuracy (S : VerifiedScheme f o p) (x : E)
    (h : ℕ → ℝ) {i : ℕ} (hi : i ∈ Finset.Icc 1 p) (hh : 0 < h i) :
    ‖S.oracle x h i - iteratedFDeriv ℝ i f x‖ ≤ S.errorMultiplier i * h i := by
  by_cases hl : i ≤ o
  · simp [errorMultiplier, hl]
  · have hhigh : i ∈ Finset.Icc (o + 1) p :=
      Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hi).2⟩
    rw [S.oracle_high x h hhigh]
    exact (S.accuracy i hhigh x _ (requestedMesh_pos hh) (requestedMesh_le_one _)).trans
      (by simpa only [errorMultiplier, ite_eq_right hl] using
        (mul_le_mul_of_nonneg_left (requestedMesh_le (h i))
          (S.multiplier_nonneg i hhigh)))

/-- The fixed finite cost of a full positive-order tensor batch. Each directly available
positive derivative is queried once; each higher-order stencil pays its fixed sample count. -/
def VerifiedScheme.batchCost (S : VerifiedScheme f o p) : ℕ :=
  o + ∑ i ∈ (Finset.Icc (o + 1) p).attach, (S.stencil i.val i.property).size

/-- A complete batch's actual low-degree oracle-query schedule. This eager schedule can
repeat points or degrees and pays for every such query explicitly. -/
def VerifiedScheme.batchQueries (S : VerifiedScheme f o p) (x : E) (h : ℕ → ℝ) :
    List (E × Fin (o + 1)) :=
  (List.finRange o).map (fun j => (x, ⟨j.val + 1, by omega⟩)) ++
    (Finset.Icc (o + 1) p).attach.toList.flatMap (fun i =>
      (S.stencil i.val i.property).queries x (requestedMesh (h i.val)))

/-- The restricted fixed batch cost pays once for each available positive order and for
every sample of each retained original stencil. It is independent of points and requests. -/
theorem VerifiedScheme.restrictOrder_batchCost (S : VerifiedScheme f o p) {q : ℕ}
    (hoq : o ≤ q) (hqp : q ≤ p) :
    (S.restrictOrder hoq hqp).batchCost =
      o + ∑ i ∈ (Finset.Icc (o + 1) q).attach, (S.stencil i.val
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp i.property).1,
          (Finset.mem_Icc.mp i.property).2.trans hqp⟩)).size := rfl

/-- Restriction schedules the same queries of each retained original stencil. Query degrees
remain at most the same available order, and the list retains every repeated sample. -/
theorem VerifiedScheme.restrictOrder_batchQueries (S : VerifiedScheme f o p) {q : ℕ}
    (hoq : o ≤ q) (hqp : q ≤ p) (x : E) (h : ℕ → ℝ) :
    (S.restrictOrder hoq hqp).batchQueries x h =
      (List.finRange o).map (fun j => (x, (⟨j.val + 1, by omega⟩ : Fin (o + 1)))) ++
        (Finset.Icc (o + 1) q).attach.toList.flatMap (fun i =>
          (S.stencil i.val (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp i.property).1,
            (Finset.mem_Icc.mp i.property).2.trans hqp⟩)).queries x
              (requestedMesh (h i.val))) := rfl

/-- Every full batch uses the same finite number of low-degree queries before any
requested accuracy is selected. No hidden accuracy-dependent stencil enlargement occurs. -/
@[simp] theorem VerifiedScheme.batchQueries_length (S : VerifiedScheme f o p)
    (x : E) (h : ℕ → ℝ) : (S.batchQueries x h).length = S.batchCost := by
  simp only [batchQueries, List.length_append, List.length_map, List.length_finRange,
    List.length_flatMap, Stencil.queries_length, batchCost]
  congr 1
  exact Finset.sum_map_toList _ _

/-- Expand exact objective calls and complete approximate tensor batches into the actual
low-degree query list of the finite stencils, preserving every repeated query. -/
def VerifiedScheme.expandedQueries (S : VerifiedScheme f o p) (values : List E)
    (batches : List (E × (ℕ → ℝ))) : List (E × Fin (o + 1)) :=
  values.map (fun x => (x, 0)) ++ batches.flatMap (fun b => S.batchQueries b.1 b.2)

/-- Finite expansion gives its exact query count; the multiplier is independent of all
requested accuracies in the batch list. -/
@[simp] theorem VerifiedScheme.expandedQueries_length (S : VerifiedScheme f o p)
    (values : List E) (batches : List (E × (ℕ → ℝ))) :
    (S.expandedQueries values batches).length = values.length + S.batchCost * batches.length := by
  simp [expandedQueries, List.length_flatMap, Nat.mul_comm]

/-- Bounds on actual objective and batch logs transfer to the expanded low-degree log. -/
theorem VerifiedScheme.expandedQueries_length_le (S : VerifiedScheme f o p)
    (values : List E) (batches : List (E × (ℕ → ℝ))) {F D : ℝ}
    (hF : (values.length : ℝ) ≤ F) (hD : (batches.length : ℝ) ≤ D) :
    ((S.expandedQueries values batches).length : ℝ) ≤ F + S.batchCost * D := by
  rw [S.expandedQueries_length]
  push_cast
  exact add_le_add hF (mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _))

end FiniteDerivativeStencil
