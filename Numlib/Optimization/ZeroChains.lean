import Numlib.Analysis.Calculus.Gradient
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Higher-order coordinate support and zero chains

Mixed partial derivatives are evaluations of the actual iterated Fréchet derivative on
coordinate basis vectors. A coordinate is exposed if it occurs in any nonzero mixed partial
of positive order at most the oracle order. Zero-respecting traces retain the union of these
supports over every previous query, starting at zero. Coordinates use zero-based `Fin n`
indices; a chain can expose at most one new coordinate at each query.
-/

noncomputable section
open scoped ContDiff ENNReal

namespace Optimization.ZeroChains

/-- Finite-dimensional real Euclidean coordinate space. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n p : ℕ}

/-- The coordinates on which a vector is nonzero. -/
def coordinateSupport (x : Space n) : Set (Fin n) := {i | x i ≠ 0}

/-- Coordinate support has the usual nonvanishing membership test. -/
@[simp] theorem mem_coordinateSupport (x : Space n) (i : Fin n) :
    i ∈ coordinateSupport x ↔ x i ≠ 0 := Iff.rfl

/-- The zero vector exposes no coordinates, including in dimension zero. -/
@[simp] theorem coordinateSupport_zero : coordinateSupport (0 : Space n) = ∅ := by
  ext i
  simp [coordinateSupport]

/-- Mixed basis evaluation of the actual derivative of order `q`. -/
def mixedPartial (q : ℕ) (f : Space n → ℝ) (x : Space n) (v : Fin q → Fin n) : ℝ :=
  iteratedFDeriv ℝ q f x (fun a => EuclideanSpace.single (v a) 1)

/-- A coordinate occurs in some nonzero mixed partial of order between one and `p`.
All positions of the mixed partial are included, independently of tensor symmetry. -/
def derivativeSupport (p : ℕ) (f : Space n → ℝ) (x : Space n) : Set (Fin n) :=
  {i | ∃ q, 1 ≤ q ∧ q ≤ p ∧ ∃ v : Fin q → Fin n,
    (∃ a, v a = i) ∧ mixedPartial q f x v ≠ 0}

/-- Membership exhibits an actual nonzero mixed partial containing the coordinate. -/
@[simp] theorem mem_derivativeSupport (f : Space n → ℝ) (x : Space n) (i : Fin n) :
    i ∈ derivativeSupport p f x ↔ ∃ q, 1 ≤ q ∧ q ≤ p ∧ ∃ v : Fin q → Fin n,
      (∃ a, v a = i) ∧ mixedPartial q f x v ≠ 0 := Iff.rfl

/-- An unexposed coordinate vanishes in every relevant mixed partial containing it. -/
theorem not_mem_derivativeSupport_iff (f : Space n → ℝ) (x : Space n) (i : Fin n) :
    i ∉ derivativeSupport p f x ↔ ∀ q, 1 ≤ q → q ≤ p → ∀ v : Fin q → Fin n,
      (∃ a, v a = i) → mixedPartial q f x v = 0 := by
  simp only [mem_derivativeSupport, not_exists, not_and, not_not]

/-- A value-only oracle exposes no derivative coordinates. -/
@[simp] theorem derivativeSupport_zero (f : Space n → ℝ) (x : Space n) :
    derivativeSupport 0 f x = ∅ := by
  ext i
  simp only [mem_derivativeSupport, Set.mem_empty_iff_false, iff_false]
  rintro ⟨q, hq, hqp, _⟩
  omega

/-- Increasing the oracle order only adds exposed coordinates. -/
theorem derivativeSupport_mono {r : ℕ} (hpr : p ≤ r) (f : Space n → ℝ) (x : Space n) :
    derivativeSupport p f x ⊆ derivativeSupport r f x := by
  rintro i ⟨q, hq, hqp, v, hv, hne⟩
  exact ⟨q, hq, hqp.trans hpr, v, hv, hne⟩

/-- First mixed partials are exactly gradient coordinates. -/
@[simp] theorem mixedPartial_one (f : Space n → ℝ) (x : Space n) (v : Fin 1 → Fin n) :
    mixedPartial 1 f x v = gradient f x (v 0) := by
  simp [mixedPartial, iteratedFDeriv_one_apply, EuclideanSpace.gradient_apply]

/-- A first-order oracle exposes precisely the nonzero gradient coordinates. -/
theorem derivativeSupport_one (f : Space n → ℝ) (x : Space n) :
    derivativeSupport 1 f x = coordinateSupport (gradient f x) := by
  ext i
  constructor
  · rintro ⟨q, hq, hqp, v, ⟨a, ha⟩, hne⟩
    have hq1 : q = 1 := by omega
    subst q
    have ha0 : a = 0 := Fin.eq_zero a
    subst a
    simpa only [mem_coordinateSupport, mixedPartial_one, ha] using hne
  · intro hi
    exact ⟨1, le_refl _, le_refl _, fun _ => i, ⟨0, rfl⟩, by simpa using hi⟩

/-- Coordinates strictly before the zero-based cutoff `k`. -/
def initialCoordinates (n k : ℕ) : Set (Fin n) := {i | i.val < k}

/-- Initial-coordinate membership is an index inequality. -/
@[simp] theorem mem_initialCoordinates (i : Fin n) (k : ℕ) :
    i ∈ initialCoordinates n k ↔ i.val < k := Iff.rfl

/-- Having support before a cutoff is equivalent to vanishing on its entire tail. -/
theorem coordinateSupport_subset_initial_iff (x : Space n) (k : ℕ) :
    coordinateSupport x ⊆ initialCoordinates n k ↔ ∀ i : Fin n, k ≤ i.val → x i = 0 := by
  constructor
  · intro h i hi
    by_contra hne
    exact (Nat.not_lt_of_ge hi) (h hne)
  · intro h i hi
    by_contra hnot
    exact hi (h i (Nat.le_of_not_gt hnot))

/-- A `C^p` zero chain exposes at most the next coordinate beyond every vanishing tail. -/
structure IsZeroChain (p : ℕ) (f : Space n → ℝ) : Prop where
  smooth : ContDiff ℝ p f
  support : ∀ k x, coordinateSupport x ⊆ initialCoordinates n k →
    derivativeSupport p f x ⊆ initialCoordinates n (k + 1)

/-- The order-zero branch imposes only continuity, because there are no positive
oracle derivative orders. -/
@[simp] theorem isZeroChain_zero_iff (f : Space n → ℝ) :
    IsZeroChain 0 f ↔ Continuous f := by
  constructor
  · exact fun h => contDiff_zero.mp h.smooth
  · intro hf
    exact ⟨contDiff_zero.mpr hf, by simp⟩

/-- The support law in vanishing-tail form, with all actual mixed partial orders retained. -/
theorem IsZeroChain.mixedPartial_eq_zero {f : Space n → ℝ} (hf : IsZeroChain p f)
    {k : ℕ} {x : Space n} (hx : ∀ i : Fin n, k ≤ i.val → x i = 0)
    {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (v : Fin q → Fin n)
    {i : Fin n} (hi : k + 1 ≤ i.val) (hv : ∃ a, v a = i) :
    mixedPartial q f x v = 0 := by
  apply (not_mem_derivativeSupport_iff f x i).mp _ q hq hqp v hv
  intro hmem
  exact (Nat.not_lt_of_ge hi) (hf.support k x
    ((coordinateSupport_subset_initial_iff x k).mpr hx) hmem)

/-- Introduction and elimination for a zero chain directly in terms of actual vanishing
mixed partials on every coordinate tail. -/
theorem isZeroChain_iff (f : Space n → ℝ) :
    IsZeroChain p f ↔ ContDiff ℝ p f ∧
      ∀ k x, (∀ i : Fin n, k ≤ i.val → x i = 0) →
      ∀ q, 1 ≤ q → q ≤ p → ∀ v : Fin q → Fin n,
      (∃ a, k + 1 ≤ (v a).val) → mixedPartial q f x v = 0 := by
  constructor
  · intro hf
    refine ⟨hf.smooth, ?_⟩
    rintro k x hx q hq hqp v ⟨a, ha⟩
    exact hf.mixedPartial_eq_zero hx hq hqp v ha ⟨a, rfl⟩
  · rintro ⟨hsmooth, hzero⟩
    refine ⟨hsmooth, ?_⟩
    intro k x hx i hi
    by_contra hout
    obtain ⟨q, hq, hqp, v, ⟨a, ha⟩, hne⟩ := hi
    apply hne
    apply hzero k x ((coordinateSupport_subset_initial_iff x k).mp hx) q hq hqp v
    exact ⟨a, by simpa only [ha] using Nat.le_of_not_gt hout⟩

/-- Pullback of an objective along an actual continuous linear coordinate map. -/
def pullback {m : ℕ} (L : Space m →L[ℝ] Space n) (f : Space n → ℝ) : Space m → ℝ :=
  f ∘ L

/-- Every mixed derivative of a linear pullback evaluates the original derivative on the
transformed coordinate vectors. This also covers dimension-increasing resisting rotations. -/
theorem mixedPartial_pullback {m : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    {q : ℕ} (hq : q ≤ p) (L : Space m →L[ℝ] Space n) (x : Space m)
    (v : Fin q → Fin m) :
    mixedPartial q (pullback L f) x v =
      iteratedFDeriv ℝ q f (L x) (fun a => L (EuclideanSpace.single (v a) 1)) := by
  unfold mixedPartial pullback
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hq)]
  rfl

/-- Pullback by the adjoint of an isometric embedding, the rectangular orthonormal
rotation action used by a resisting oracle. Canonical coordinate supports are not assumed
invariant under this action. -/
def rotate {m : ℕ} (U : Space n →ₗᵢ[ℝ] Space m) (f : Space n → ℝ) : Space m → ℝ :=
  pullback U.toContinuousLinearMap.adjoint f

/-- The rotated objective has the original derivative on the rotated coordinate vectors. -/
theorem mixedPartial_rotate {m : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    {q : ℕ} (hq : q ≤ p) (U : Space n →ₗᵢ[ℝ] Space m) (x : Space m)
    (v : Fin q → Fin m) :
    mixedPartial q (rotate U f) x v =
      iteratedFDeriv ℝ q f (U.toContinuousLinearMap.adjoint x)
        (fun a => U.toContinuousLinearMap.adjoint (EuclideanSpace.single (v a) 1)) :=
  mixedPartial_pullback hf hq U.toContinuousLinearMap.adjoint x v

/-- Scalar input and output rescaling; the source's `μ₁ f(x/μ₂)` uses `b = μ₂⁻¹`. -/
def rescale (a b : ℝ) (f : Space n → ℝ) (x : Space n) : ℝ := a * f (b • x)

/-- Actual mixed derivatives under scalar rescaling, including order zero and zero scalars. -/
theorem mixedPartial_rescale {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    {q : ℕ} (hq : q ≤ p) (a b : ℝ) (x : Space n) (v : Fin q → Fin n) :
    mixedPartial q (rescale a b f) x v = a * b ^ q * mixedPartial q f (b • x) v := by
  let B : Space n →L[ℝ] Space n := b • ContinuousLinearMap.id ℝ (Space n)
  have hcomp : ContDiff ℝ p (f ∘ B) := hf.comp B.contDiff
  unfold mixedPartial rescale
  change iteratedFDeriv ℝ q (fun y => a • (f ∘ B) y) x _ = _
  rw [iteratedFDeriv_const_smul_apply' (hcomp.of_le (by exact_mod_cast hq)).contDiffAt,
    B.iteratedFDeriv_comp_right hf x (by exact_mod_cast hq)]
  simp only [smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change a * (iteratedFDeriv ℝ q f (b • x))
    (fun i => b • EuclideanSpace.single (v i) 1) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp [mul_assoc]

/-- Rescaling cannot introduce a previously unexposed derivative coordinate. -/
theorem derivativeSupport_rescale_subset {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    (a b : ℝ) (x : Space n) :
    derivativeSupport p (rescale a b f) x ⊆ derivativeSupport p f (b • x) := by
  rintro i ⟨q, hq, hqp, v, hv, hne⟩
  refine ⟨q, hq, hqp, v, hv, ?_⟩
  intro hz
  exact hne (by rw [mixedPartial_rescale hf hqp, hz, mul_zero])

/-- Nonzero scalar input and output preserve exactly every derivative coordinate support. -/
theorem derivativeSupport_rescale {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (x : Space n) :
    derivativeSupport p (rescale a b f) x = derivativeSupport p f (b • x) := by
  apply Set.Subset.antisymm (derivativeSupport_rescale_subset hf a b x)
  rintro i ⟨q, hq, hqp, v, hv, hne⟩
  refine ⟨q, hq, hqp, v, hv, ?_⟩
  rw [mixedPartial_rescale hf hqp]
  exact mul_ne_zero (mul_ne_zero ha (pow_ne_zero _ hb)) hne

/-- Zero output scaling exposes no derivative coordinate at any positive order. -/
@[simp] theorem derivativeSupport_rescale_zero_output {f : Space n → ℝ}
    (hf : ContDiff ℝ p f) (b : ℝ) (x : Space n) :
    derivativeSupport p (rescale 0 b f) x = ∅ := by
  ext i
  simp only [mem_derivativeSupport, Set.mem_empty_iff_false, iff_false]
  rintro ⟨q, hq, hqp, v, hv, hne⟩
  exact hne (by rw [mixedPartial_rescale hf hqp]; simp)

/-- Zero input scaling is constant and exposes no coordinate, including for order zero. -/
@[simp] theorem derivativeSupport_rescale_zero_input {f : Space n → ℝ}
    (hf : ContDiff ℝ p f) (a : ℝ) (x : Space n) :
    derivativeSupport p (rescale a 0 f) x = ∅ := by
  ext i
  simp only [mem_derivativeSupport, Set.mem_empty_iff_false, iff_false]
  rintro ⟨q, hq, hqp, v, hv, hne⟩
  exact hne (by rw [mixedPartial_rescale hf hqp]; simp [Nat.ne_zero_of_lt hq])

/-- Scalar rescaling preserves a zero chain, including zero output and zero input scalars. -/
theorem IsZeroChain.rescale {f : Space n → ℝ} (hf : IsZeroChain p f) (a b : ℝ) :
    IsZeroChain p (rescale a b f) := by
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ (p : ℕ∞ω) (fun x : Space n => a * f (b • x))
    exact (hf.smooth.comp (contDiff_id.const_smul b)).const_smul a
  intro k x hx i hi
  apply hf.support k (b • x) _ (derivativeSupport_rescale_subset hf.smooth a b x hi)
  intro j hj
  apply hx
  intro hz
  exact hj (by simp [hz])

/-- A zero-respecting trace starts at zero and uses only derivative coordinates exposed
at some previous query. This records the full oracle history rather than only the last query. -/
structure IsZeroRespecting (p : ℕ) (f : Space n → ℝ) (x : ℕ → Space n) : Prop where
  initial : x 0 = 0
  support : ∀ k, coordinateSupport (x (k + 1)) ⊆
    {i | ∃ j ≤ k, i ∈ derivativeSupport p f (x j)}

/-- The history support rule equivalently preserves every coordinate absent from all
positive derivative orders at all previous iterates. -/
theorem IsZeroRespecting.coordinate_eq_zero {f : Space n → ℝ} {x : ℕ → Space n}
    (hx : IsZeroRespecting p f x) (k : ℕ) (i : Fin n)
    (hi : ∀ j ≤ k, i ∉ derivativeSupport p f (x j)) : x (k + 1) i = 0 := by
  by_contra hne
  obtain ⟨j, hj, hs⟩ := hx.support k hne
  exact hi j hj hs

/-- Each query of a zero-respecting method on a zero chain can reveal at most one new
coordinate, so the `k`th iterate is supported in the first `k` coordinates. -/
theorem IsZeroChain.support_iterate {f : Space n → ℝ} (hf : IsZeroChain p f)
    {x : ℕ → Space n} (hx : IsZeroRespecting p f x) (k : ℕ) :
    coordinateSupport (x k) ⊆ initialCoordinates n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [hx.initial]
    | succ k =>
      intro i hi
      obtain ⟨j, hj, hs⟩ := hx.support k hi
      have hprev := ih j (by omega)
      have hcoord := hf.support j (x j) hprev hs
      change i.val < k + 1
      change i.val < j + 1 at hcoord
      omega

end Optimization.ZeroChains
