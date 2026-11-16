/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Incenter.Basic
import Mathlib.Geometry.Euclidean.Triangle

/-!
# The shape of a triangle: diameter, inradius and angles

Let $K$ be a triangle with vertices $p_0, p_1, p_2$ in a Euclidean affine space of any dimension,
with the indices read modulo $3$. Write $\theta_i$ for the angle of $K$ at $p_i$, $h_i$ for the
height of $K$ at $p_i$ (the distance from $p_i$ to the line through the other two vertices), $r_K$
for the inradius, and $h_K = \operatorname{diam} K$ for the diameter, which is the longest side. In
the finite element method the shape of $K$ is measured by the ratio $h_K / \rho_K$, where
$\rho_K = 2 r_K$ is the diameter of the inscribed circle. This ratio is bounded exactly when the
angles of $K$ are bounded away from $0$. This module proves the two quantitative halves of that
equivalence: $r_K \le h_K \sin\theta_i$ for every $i$, and $h_K \sin^2\alpha \le 3 r_K$ when every
angle is at least $\alpha \in (0, \pi/2]$.

For a simplex of any dimension $n \ge 1$, the module also proves $1/r = \sum_i 1/h_i$ and the two
inequalities that follow from it: $r \le h_i$ for every $i$, and $m \le (n + 1) r$ when every height
is at least $m > 0$.

## Main definitions

* `Affine.Simplex.triangleAngle`: the angle $\theta_i = \angle p_{i+1} p_i p_{i+2}$ of a triangle at
  its vertex $p_i$.

## Main results

* `Affine.Simplex.inv_inradius_eq_sum_inv_height`: for a simplex, $1/r = \sum_i 1/h_i$.
* `Affine.Simplex.inradius_le_height`: for a simplex, $r \le h_i$ for every $i$.
* `Affine.Simplex.le_card_mul_inradius`: for an $n$-simplex whose heights are all at least $m > 0$,
  $m \le (n + 1) r$.
* `Affine.Simplex.height_eq_dist_mul_sin_angle`: in a triangle with vertices $p_i, p_j, p_k$,
  $h_i = |p_i p_k| \sin \angle p_j p_k p_i$.
* `Affine.Simplex.height_mul_sin_triangleAngle_eq`: in a triangle,
  $h_i \sin\theta_i = h_j \sin\theta_j$ for all $i$ and $j$.
* `Affine.Simplex.exists_dist_eq_diam`: the diameter of a triangle is the length of one of its
  sides.
* `Affine.Simplex.inradius_le_diam_mul_sin_triangleAngle`: $r_K \le h_K \sin\theta_i$ for every
  angle $\theta_i$.
* `Affine.Simplex.diam_mul_sin_sq_le`: if every angle is at least $\alpha \in (0, \pi/2]$, then
  $h_K \sin^2\alpha \le 3 r_K$.

## Proof outline

Everything rests on the identity $h_i = |p_i p_k| \sin \angle p_j p_k p_i$, where $j$ and $k$ are
the other two vertices. It has two consequences. First, the heights at the two ends of a side
satisfy $h_i \sin\theta_i = h_j \sin\theta_j$, so no two heights differ by more than a factor
$1/\sin\theta_{\min}$. Second, the height at an end of the longest side is $h_K \sin\theta$ for the
angle $\theta$ at the other end of that side, so some height is at least $h_K \sin\theta_{\min}$.
Together with $1/r = \sum_i 1/h_i$, these bound the inradius above and below by multiples of the
diameter.

## Implementation notes

* The triangle is an `Affine.Simplex ℝ P 2`. The height $h_i$ is Mathlib's `Affine.Simplex.height`,
  the inradius $r$ is `Affine.Simplex.inradius`, and the diameter $h_K$ is
  `Metric.diam (Set.range s.points)`.
* The formula $1/r = \sum_i 1/h_i$ is Mathlib's `Affine.Simplex.inradius_eq_abs_inv_sum`, with the
  weights `Affine.Simplex.excenterWeightsUnnorm` written out.
* The results are stated with the inradius $r_K$, not with the diameter $\rho_K = 2 r_K$ of the
  inscribed circle.
-/

open EuclideanGeometry Finset

open scoped Real

namespace Real

/-- Let $0 < \alpha \le \pi/2$. If $\alpha \le \theta \le \pi - \alpha$, then
$\sin\alpha \le \sin\theta$. -/
theorem le_sin_of_le_of_le_pi_sub {α θ : ℝ} (hα : 0 < α) (hα2 : α ≤ π / 2) (h1 : α ≤ θ)
    (h2 : θ ≤ π - α) : Real.sin α ≤ Real.sin θ := by
  rcases le_total θ (π / 2) with h | h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
  · rw [← Real.sin_pi_sub θ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

end Real

namespace Affine.Simplex

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ### The inradius against the heights -/

/-- Let $s$ be an $n$-simplex with $n \ge 1$ in a Euclidean affine space, with heights
$h_0, \dots, h_n$ and inradius $r$. Then
$$\frac{1}{r} = \sum_{i=0}^{n} \frac{1}{h_i}.$$

Here $h_i$ is `Affine.Simplex.height`, the distance from the vertex $p_i$ to the affine span of
the other vertices. The proof is Mathlib's `Affine.Simplex.inradius_eq_abs_inv_sum`, with the
weights `Affine.Simplex.excenterWeightsUnnorm ∅` written out. -/
theorem inv_inradius_eq_sum_inv_height {n : ℕ} [NeZero n] (s : Simplex ℝ P n) :
    (s.inradius)⁻¹ = ∑ i, (s.height i)⁻¹ := by
  have hpos : 0 < ∑ i, (s.height i)⁻¹ :=
    Finset.sum_pos (fun i _ => inv_pos.2 (s.height_pos i)) ⟨0, Finset.mem_univ 0⟩
  have hw : ∑ i, s.excenterWeightsUnnorm ∅ i = ∑ i, (s.height i)⁻¹ :=
    Finset.sum_congr rfl fun i _ => by simp [Affine.Simplex.excenterWeightsUnnorm]
  rw [s.inradius_eq_abs_inv_sum, hw, abs_of_pos (inv_pos.2 hpos), inv_inv]

/-- Let $s$ be an $n$-simplex with $n \ge 1$ in a Euclidean affine space, with heights
$h_0, \dots, h_n$ and inradius $r$. Then $r \le h_i$ for every $i$. -/
theorem inradius_le_height {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.inradius ≤ s.height i := by
  have hle : (s.height i)⁻¹ ≤ (s.inradius)⁻¹ := by
    rw [s.inv_inradius_eq_sum_inv_height]
    exact Finset.single_le_sum (fun j _ => (inv_pos.2 (s.height_pos j)).le) (Finset.mem_univ i)
  exact (inv_le_inv₀ (s.height_pos i) s.inradius_pos).1 hle

/-- Let $s$ be an $n$-simplex with $n \ge 1$ in a Euclidean affine space, with heights
$h_0, \dots, h_n$ and inradius $r$, and let $m > 0$. If $m \le h_i$ for every $i$, then
$m \le (n + 1) r$. -/
theorem le_card_mul_inradius {n : ℕ} [NeZero n] (s : Simplex ℝ P n) {m : ℝ} (hm : 0 < m)
    (h : ∀ i, m ≤ s.height i) : m ≤ (n + 1) * s.inradius := by
  have hr := s.inradius_pos
  have hle : (s.inradius)⁻¹ ≤ (n + 1) * m⁻¹ := by
    rw [s.inv_inradius_eq_sum_inv_height]
    calc ∑ i, (s.height i)⁻¹ ≤ ∑ _i : Fin (n + 1), m⁻¹ :=
          Finset.sum_le_sum fun i _ => (inv_le_inv₀ (s.height_pos i) hm).2 (h i)
      _ = (n + 1) * m⁻¹ := by simp [mul_comm]
  have hkey : m * (s.inradius)⁻¹ ≤ (n + 1) := by
    have := mul_le_mul_of_nonneg_left hle hm.le
    rwa [show m * ((n + 1) * m⁻¹) = (n + 1) by field_simp] at this
  calc m = (m * (s.inradius)⁻¹) * s.inradius := by field_simp
    _ ≤ (n + 1) * s.inradius := mul_le_mul_of_nonneg_right hkey hr.le

/-! ### The height of a triangle through an angle -/

/-- Let $s$ be a triangle in a Euclidean affine space, and let $i, j, k$ be its three vertex
indices, so that $j$ and $k$ are the two indices other than $i$. Then the height of $s$ at $p_i$
is
$$h_i = |p_i p_k| \sin \angle p_j p_k p_i.$$

The foot of the altitude from $p_i$ lies on the line through $p_j$ and $p_k$. The angle at $p_k$
between this line and $p_i$ is therefore the angle of the triangle at $p_k$ or its supplement,
and the two have the same sine. In Lean the indices are given by $i \ne j$, $i \ne k$ and
$\{i\}^c = \{j, k\}$. -/
theorem height_eq_dist_mul_sin_angle (s : Simplex ℝ P 2) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hcompl : ({i}ᶜ : Set (Fin 3)) = {j, k}) :
    s.height i
      = dist (s.points i) (s.points k) * Real.sin (∠ (s.points j) (s.points k) (s.points i)) := by
  set F := s.altitudeFoot i with hF
  have hperp : ∀ m : Fin 3, i ≠ m →
      inner ℝ (s.points m -ᵥ F) (s.points i -ᵥ F) = (0 : ℝ) := fun m h =>
    s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero h
  have hright : ∠ (s.points i) F (s.points k) = π / 2 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle_comm,
      ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    exact hperp k hik
  have hmain := EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two hright
  have hmem : F ∈ affineSpan ℝ ({s.points k, s.points j} : Set P) := by
    have h := s.altitudeFoot_mem_affineSpan_image_compl i
    rw [hcompl] at h
    have himg : s.points '' {j, k} = ({s.points k, s.points j} : Set P) := by
      simp [Set.image_insert_eq, Set.pair_comm]
    rwa [himg] at h
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hmem
  have hvsub : F -ᵥ s.points k = t • (s.points j -ᵥ s.points k) := by
    rw [← ht, AffineMap.lineMap_apply, vadd_vsub]
  have hsin : Real.sin (∠ F (s.points k) (s.points i))
      = Real.sin (∠ (s.points j) (s.points k) (s.points i)) := by
    rw [EuclideanGeometry.angle, EuclideanGeometry.angle, hvsub]
    rcases lt_trichotomy t 0 with ht0 | ht0 | ht0
    · rw [InnerProductGeometry.angle_smul_left_of_neg _ _ ht0,
        InnerProductGeometry.angle_neg_left, Real.sin_pi_sub]
    · subst ht0
      have hFk : F = s.points k :=
        vsub_eq_zero_iff_eq.1 (by rw [hvsub, zero_smul])
      have hperpj : inner ℝ (s.points j -ᵥ s.points k) (s.points i -ᵥ s.points k) = (0 : ℝ) := by
        have h := hperp j hij
        rwa [hFk] at h
      rw [zero_smul, InnerProductGeometry.angle_zero_left,
        (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).1 hperpj]
    · rw [InnerProductGeometry.angle_smul_left_of_pos _ _ ht0]
  rw [Affine.Simplex.height, ← hmain, hsin]
  ring

/-! ### The angles of a triangle -/

/-- The **angle** $\theta_i = \angle p_{i+1} p_i p_{i+2}$ of a triangle $s$ with vertices
$p_0, p_1, p_2$ at its vertex $p_i$, with the indices read modulo $3$.

It is the unoriented angle `EuclideanGeometry.angle`, with values in $[0, \pi]$. -/
noncomputable def triangleAngle (s : Simplex ℝ P 2) (i : Fin 3) : ℝ :=
  ∠ (s.points (i + 1)) (s.points i) (s.points (i + 2))

/-- An angle of a triangle is nonnegative: $0 \le \theta_i$. -/
theorem triangleAngle_nonneg (s : Simplex ℝ P 2) (i : Fin 3) : 0 ≤ s.triangleAngle i :=
  EuclideanGeometry.angle_nonneg _ _ _

/-- An angle of a triangle is at most $\pi$: $\theta_i \le \pi$. -/
theorem triangleAngle_le_pi (s : Simplex ℝ P 2) (i : Fin 3) : s.triangleAngle i ≤ π :=
  EuclideanGeometry.angle_le_pi _ _ _

/-- The sine of an angle of a triangle is nonnegative: $0 \le \sin\theta_i$. -/
theorem sin_triangleAngle_nonneg (s : Simplex ℝ P 2) (i : Fin 3) :
    0 ≤ Real.sin (s.triangleAngle i) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (s.triangleAngle_nonneg i) (s.triangleAngle_le_pi i)

/-- The sine of an angle of a triangle is at most $1$: $\sin\theta_i \le 1$. -/
theorem sin_triangleAngle_le_one (s : Simplex ℝ P 2) (i : Fin 3) :
    Real.sin (s.triangleAngle i) ≤ 1 :=
  Real.sin_le_one _

/-- The angles of a triangle sum to $\pi$: $\theta_0 + \theta_1 + \theta_2 = \pi$. -/
theorem sum_triangleAngle (s : Simplex ℝ P 2) :
    s.triangleAngle 0 + s.triangleAngle 1 + s.triangleAngle 2 = π := by
  have hne : s.points 0 ≠ s.points 1 := fun h =>
    (by decide : (0 : Fin 3) ≠ 1) (s.independent.injective h)
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (s.points 2) hne.symm
  simp only [triangleAngle]
  rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  rw [EuclideanGeometry.angle_comm (s.points 1) (s.points 0) (s.points 2),
    EuclideanGeometry.angle_comm (s.points 0) (s.points 2) (s.points 1),
    EuclideanGeometry.angle_comm (s.points 2) (s.points 1) (s.points 0)]
  linarith [h]

/-- In $\mathbb{Z}/3$, $i + 1 + 1 = i + 2$ for every index $i$ of `Fin 3`. -/
theorem finAdd_one_one (i : Fin 3) : i + 1 + 1 = i + 2 := by revert i; decide

/-- In $\mathbb{Z}/3$, $i + 1 + 2 = i$ for every index $i$ of `Fin 3`. -/
theorem finAdd_one_two (i : Fin 3) : i + 1 + 2 = i := by revert i; decide

/-- In $\mathbb{Z}/3$, $i + 2 + 1 = i$ for every index $i$ of `Fin 3`. -/
theorem finAdd_two_one (i : Fin 3) : i + 2 + 1 = i := by revert i; decide

/-- In $\mathbb{Z}/3$, $i + 2 + 2 = i + 1$ for every index $i$ of `Fin 3`. -/
theorem finAdd_two_two (i : Fin 3) : i + 2 + 2 = i + 1 := by revert i; decide

/-- In a triangle with vertices $p_0, p_1, p_2$, the height at $p_i$ is given by the angle at the
next vertex:
$$h_i = |p_i p_{i+1}| \sin\theta_{i+1}.$$
-/
theorem height_eq_dist_mul_sin_triangleAngle_succ (s : Simplex ℝ P 2) (i : Fin 3) :
    s.height i = dist (s.points i) (s.points (i + 1)) * Real.sin (s.triangleAngle (i + 1)) := by
  have hcompl : ({i}ᶜ : Set (Fin 3)) = {i + 2, i + 1} := by
    fin_cases i <;> (ext x; fin_cases x <;> simp)
  have h := s.height_eq_dist_mul_sin_angle (i := i) (j := i + 2) (k := i + 1)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) hcompl
  rw [h, triangleAngle, finAdd_one_one, finAdd_one_two]

/-- In a triangle with vertices $p_0, p_1, p_2$, the height at $p_i$ is given by the angle at the
previous vertex:
$$h_i = |p_i p_{i+2}| \sin\theta_{i+2}.$$
-/
theorem height_eq_dist_mul_sin_triangleAngle_succ_succ (s : Simplex ℝ P 2) (i : Fin 3) :
    s.height i = dist (s.points i) (s.points (i + 2)) * Real.sin (s.triangleAngle (i + 2)) := by
  have hcompl : ({i}ᶜ : Set (Fin 3)) = {i + 1, i + 2} := by
    fin_cases i <;> (ext x; fin_cases x <;> simp)
  have h := s.height_eq_dist_mul_sin_angle (i := i) (j := i + 1) (k := i + 2)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) hcompl
  rw [h, triangleAngle, finAdd_two_one, finAdd_two_two, EuclideanGeometry.angle_comm]

/-- **The heights at the two ends of a side are inversely proportional to the sines of the angles
there.** In a triangle with vertices $p_0, p_1, p_2$, for every $i$,
$$h_i \sin\theta_i = h_{i+1} \sin\theta_{i+1}.$$

Both products equal $|p_i p_{i+1}| \sin\theta_i \sin\theta_{i+1}$. -/
theorem height_mul_sin_triangleAngle_comm (s : Simplex ℝ P 2) (i : Fin 3) :
    s.height i * Real.sin (s.triangleAngle i)
      = s.height (i + 1) * Real.sin (s.triangleAngle (i + 1)) := by
  rw [s.height_eq_dist_mul_sin_triangleAngle_succ i,
    s.height_eq_dist_mul_sin_triangleAngle_succ_succ (i + 1), finAdd_one_two,
    dist_comm (s.points (i + 1)) (s.points i)]
  ring

/-- In a triangle with vertices $p_0, p_1, p_2$, any two heights satisfy
$$h_i \sin\theta_i = h_j \sin\theta_j.$$
-/
theorem height_mul_sin_triangleAngle_eq (s : Simplex ℝ P 2) (i j : Fin 3) :
    s.height i * Real.sin (s.triangleAngle i)
      = s.height j * Real.sin (s.triangleAngle j) := by
  have e0 := s.height_mul_sin_triangleAngle_comm 0
  have e1 := s.height_mul_sin_triangleAngle_comm 1
  rw [show (0 : Fin 3) + 1 = 1 from rfl] at e0
  rw [show (1 : Fin 3) + 1 = 2 from rfl] at e1
  have key : ∀ k : Fin 3, s.height k * Real.sin (s.triangleAngle k)
      = s.height 0 * Real.sin (s.triangleAngle 0) := by
    intro k
    fin_cases k
    · rfl
    · exact e0.symm
    · exact (e0.trans e1).symm
  rw [key i, key j]

/-! ### The diameter of a triangle -/

/-- Every side of a triangle is at most its diameter: $|p_i p_j| \le \operatorname{diam}\{p_0, p_1,
p_2\}$. -/
theorem dist_le_diam (s : Simplex ℝ P 2) (i j : Fin 3) :
    dist (s.points i) (s.points j) ≤ Metric.diam (Set.range s.points) :=
  Metric.dist_le_diam_of_mem (Set.finite_range s.points).isBounded ⟨i, rfl⟩ ⟨j, rfl⟩

/-- A triangle has positive diameter, because its vertices are distinct. -/
theorem diam_pos (s : Simplex ℝ P 2) : 0 < Metric.diam (Set.range s.points) := by
  refine lt_of_lt_of_le ?_ (s.dist_le_diam 0 1)
  refine dist_pos.2 fun h => ?_
  exact (by decide : (0 : Fin 3) ≠ 1) (s.independent.injective h)

/-- The diameter of a triangle is the length of one of its sides: there is an $i$ with $|p_i
p_{i+1}| = \operatorname{diam}\{p_0, p_1, p_2\}$. -/
theorem exists_dist_eq_diam (s : Simplex ℝ P 2) :
    ∃ i : Fin 3, dist (s.points i) (s.points (i + 1)) = Metric.diam (Set.range s.points) := by
  set M := max (dist (s.points 0) (s.points 1))
    (max (dist (s.points 1) (s.points 2)) (dist (s.points 2) (s.points 0))) with hM
  have h01 : dist (s.points 0) (s.points 1) ≤ M := le_max_left _ _
  have h12 : dist (s.points 1) (s.points 2) ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have h20 : dist (s.points 2) (s.points 0) ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have h0 : (0 : ℝ) ≤ M := le_trans dist_nonneg h01
  have hDM : Metric.diam (Set.range s.points) ≤ M := by
    refine Metric.diam_le_of_forall_dist_le h0 ?_
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    fin_cases a <;> fin_cases b <;>
      simp only [dist_self] <;>
      first
        | exact h0
        | exact h01
        | exact h12
        | exact h20
        | (rw [dist_comm]; first | exact h01 | exact h12 | exact h20)
  have hMD : M ≤ Metric.diam (Set.range s.points) :=
    max_le (s.dist_le_diam 0 1) (max_le (s.dist_le_diam 1 2) (s.dist_le_diam 2 0))
  have hMeq : M = Metric.diam (Set.range s.points) := le_antisymm hMD hDM
  have hchoice : M = dist (s.points 0) (s.points 1) ∨ M = dist (s.points 1) (s.points 2)
      ∨ M = dist (s.points 2) (s.points 0) := by
    rcases max_choice (dist (s.points 0) (s.points 1))
      (max (dist (s.points 1) (s.points 2)) (dist (s.points 2) (s.points 0))) with h | h
    · exact Or.inl h
    · rcases max_choice (dist (s.points 1) (s.points 2))
        (dist (s.points 2) (s.points 0)) with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · exact Or.inr (Or.inr (h.trans h'))
  rcases hchoice with h | h | h
  · exact ⟨0, by rw [show (0 : Fin 3) + 1 = 1 from rfl, ← h, hMeq]⟩
  · exact ⟨1, by rw [show (1 : Fin 3) + 1 = 2 from rfl, ← h, hMeq]⟩
  · exact ⟨2, by rw [show (2 : Fin 3) + 1 = 0 from rfl, ← h, hMeq]⟩

/-! ### The two halves of the shape equivalence -/

/-- **The inradius is at most the diameter times the sine of every angle.** Let $K$ be a triangle
with diameter $h_K$, inradius $r_K$ and angles $\theta_0, \theta_1, \theta_2$. Then for every
$i$,
$$r_K \le h_K \sin\theta_i.$$

Thus an upper bound on the ratio $h_K / r_K$ gives a lower bound on every $\sin\theta_i$. The
proof bounds $r_K$ by the height $h_{i+2} = |p_{i+2} p_i| \sin\theta_i$. -/
theorem inradius_le_diam_mul_sin_triangleAngle (s : Simplex ℝ P 2) (i : Fin 3) :
    s.inradius ≤ Metric.diam (Set.range s.points) * Real.sin (s.triangleAngle i) := by
  have h := s.height_eq_dist_mul_sin_triangleAngle_succ (i + 2)
  rw [finAdd_two_one] at h
  calc s.inradius ≤ s.height (i + 2) := s.inradius_le_height _
    _ = dist (s.points (i + 2)) (s.points i) * Real.sin (s.triangleAngle i) := h
    _ ≤ Metric.diam (Set.range s.points) * Real.sin (s.triangleAngle i) :=
        mul_le_mul_of_nonneg_right (s.dist_le_diam _ _) (s.sin_triangleAngle_nonneg i)

/-- **A lower bound on the angles bounds the ratio of the diameter to the inradius.** Let $K$ be a
triangle with diameter $h_K$ and inradius $r_K$, and let $0 < \alpha \le \pi/2$. If every angle
of $K$ is at least $\alpha$, then
$$h_K \sin^2\alpha \le 3 r_K.$$

The height at an end of the longest side is at least $h_K \sin\alpha$. By
`Affine.Simplex.height_mul_sin_triangleAngle_eq`, every height is then at least
$h_K \sin^2\alpha$, and `Affine.Simplex.le_card_mul_inradius` gives the bound. -/
theorem diam_mul_sin_sq_le (s : Simplex ℝ P 2) {α : ℝ} (hα : 0 < α) (hα2 : α ≤ π / 2)
    (h : ∀ i, α ≤ s.triangleAngle i) :
    Metric.diam (Set.range s.points) * Real.sin α ^ 2 ≤ 3 * s.inradius := by
  have hsinpos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hsum := s.sum_triangleAngle
  have hle : ∀ i : Fin 3, s.triangleAngle i ≤ π - α := by
    intro i
    fin_cases i
    · change s.triangleAngle 0 ≤ π - α
      linarith [h 1, h 2]
    · change s.triangleAngle 1 ≤ π - α
      linarith [h 0, h 2]
    · change s.triangleAngle 2 ≤ π - α
      linarith [h 0, h 1]
  have hsin : ∀ i, Real.sin α ≤ Real.sin (s.triangleAngle i) := fun i =>
    Real.le_sin_of_le_of_le_pi_sub hα hα2 (h i) (hle i)
  obtain ⟨m, hm⟩ := s.exists_dist_eq_diam
  set D := Metric.diam (Set.range s.points) with hD
  have hDpos : 0 < D := s.diam_pos
  have hbig : D * Real.sin α ≤ s.height m := by
    rw [s.height_eq_dist_mul_sin_triangleAngle_succ m, hm]
    exact mul_le_mul_of_nonneg_left (hsin (m + 1)) hDpos.le
  have hall : ∀ j, D * Real.sin α ^ 2 ≤ s.height j := by
    intro j
    have heq := s.height_mul_sin_triangleAngle_eq m j
    have h1 : D * Real.sin α * Real.sin α ≤ s.height m * Real.sin (s.triangleAngle m) :=
      mul_le_mul hbig (hsin m) hsinpos.le (le_trans (by positivity) hbig)
    have h2 : s.height j * Real.sin (s.triangleAngle j) ≤ s.height j := by
      nlinarith [(s.height_pos j).le, s.sin_triangleAngle_le_one j]
    calc D * Real.sin α ^ 2 = D * Real.sin α * Real.sin α := by ring
      _ ≤ s.height m * Real.sin (s.triangleAngle m) := h1
      _ = s.height j * Real.sin (s.triangleAngle j) := heq
      _ ≤ s.height j := h2
  have hmpos : 0 < D * Real.sin α ^ 2 := by positivity
  have := s.le_card_mul_inradius hmpos hall
  norm_num at this
  linarith

end Affine.Simplex
