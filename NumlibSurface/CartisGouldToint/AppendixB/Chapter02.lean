import NumlibSurface.CartisGouldToint.AppendixB.Chapter02.FiniteValleySmooth

/-!
# The finite SDEX construction and its analytic properties

This module identifies the concrete Hermite construction with Appendix B.2.2–B.2.6.
The source explicitly constructs only the path up to the termination index; formulas
with unrestricted indices are used here only on those finite cells. For arbitrary
`eps ∈ (0,1]`, the integer iteration count is `ceil(eps⁻²)`. The printed exact count
is recovered separately whenever `eps⁻²` is an integer.

The source leaves the extension beyond its last interpolation node unspecified. We
choose the explicit unit transition to a constant objective, with width and midpoint
frozen. This gives a bounded C2 completion while retaining every prescribed cell and
nodal jet. At the left endpoint equation (B.2.24) is affine in x; the transverse
profile is symmetric about its moving midpoint. There is no reflection in x.

The conclusion of the proof of Lemma B.2.6 is a first *local* minimum of the complete
ray. This is the meaning formalized here, including exclusion of every earlier
nonnegative ray parameter. The global exact-search interpretation is refuted by
`finite_valley_not_global_exact`; it is not inferred from the local result.
-/

noncomputable section
open Optimization.SteepestDescentValley Set Hermite
open scoped NNReal

namespace CartisGouldToint.AppendixB.Chapter02

/-- The actual finite scalar cells, nodal data and exterior completion in (B.2.4)–(B.2.25).
Every field concerns the explicit constructed functions, not an interpolation oracle.
`cellLength` equals epsilon plus the source's linearly decreasing omega; `lengthDrop`
is the difference of successive omegas. The profile fields identify all five branches
of (B.2.19), with the exact quintic boundary jets supplied by
`lower_strip_boundary_conditions`. The terminal unit transition is our explicit choice
of the right completion, for which the source supplies no data. -/
structure FiniteValleyData (P : Parameters) : Prop where
  length_formula : ∀ k : ℕ,
    cellLength P k = P.eps + P.eps * ((P.count : ℝ) - k) / P.count
  initial_point : nodePoint P 0 = 0
  initial_value : nodeValue P 0 = 4
  node_recurrences : ∀ k < P.count,
    nodeX P (k + 1) = nodeX P k + cellLength P k ∧
      nodeY P (k + 1) = nodeY P k + cellSign k * cellLength P k ∧
        nodeValue P (k + 1) = nodeValue P k - cellLength P k ^ 2
  nodal_jets : ∀ k ≤ P.count, ∀ j ≤ 2,
    iteratedDeriv j (scalarObjective P) (nodeX P k) = objectiveJet P k j ∧
      iteratedDeriv j (scalarWidth P) (nodeX P k) = widthJet P k j ∧
        iteratedDeriv j (scalarMidpoint P) (nodeX P k) = midpointJet P k j
  objective_cells : ∀ k < P.count, ∀ x ∈ Icc (nodeX P k) (nodeX P (k + 1)),
    scalarObjective P x = nodeValue P k - cellLength P k ^ 2 *
      ((x - nodeX P k) / cellLength P k) + cellLength P k * lengthDrop P *
      (-4 * ((x - nodeX P k) / cellLength P k) ^ 3 +
        7 * ((x - nodeX P k) / cellLength P k) ^ 4 -
        3 * ((x - nodeX P k) / cellLength P k) ^ 5)
  width_cells : ∀ k < P.count, ∀ x ∈ Icc (nodeX P k) (nodeX P (k + 1)),
    scalarWidth P x = cellLength P k - lengthDrop P *
      smoothStep ((x - nodeX P k) / cellLength P k)
  midpoint_cells : ∀ k < P.count, ∀ x ∈ Icc (nodeX P k) (nodeX P (k + 1)),
    scalarMidpoint P x = nodeMidpoint P k + cellSign k * lengthDrop P / 2 *
      smoothStep ((x - nodeX P k) / cellLength P k)
  transverse_branches : ∀ p : EuclideanSpace ℝ (Fin 2),
    let d := scalarWidth P (p 0)
    let z := p 1 - scalarMidpoint P (p 0)
    (z ≤ -d / 2 - 1 → euclideanMovingProfile P p = 8 * d ^ 2) ∧
    (-z - d / 2 ∈ Icc (0 : ℝ) 1 → euclideanMovingProfile P p = strip d (-z - d / 2)) ∧
    (-d / 2 ≤ z → z ≤ d / 2 → euclideanMovingProfile P p = z ^ 2) ∧
    (z - d / 2 ∈ Icc (0 : ℝ) 1 → euclideanMovingProfile P p = strip d (z - d / 2)) ∧
    (d / 2 + 1 ≤ z → euclideanMovingProfile P p = 8 * d ^ 2)
  left_completion : ∀ x ≤ 0,
    scalarObjective P x = 4 - 2 * P.eps * x ∧
      scalarWidth P x = 2 * P.eps ∧ scalarMidpoint P x = nodeMidpoint P 0
  right_transition : ∀ x ∈ Icc (nodeX P P.count) (nodeX P P.count + 1),
    scalarObjective P x = nodeValue P P.count - P.eps * (x - nodeX P P.count) +
      P.eps * (x - nodeX P P.count) ^ 3 - P.eps / 2 * (x - nodeX P P.count) ^ 4
  right_completion : ∀ x, nodeX P P.count + 1 ≤ x →
    scalarObjective P x = nodeValue P P.count - P.eps / 2 ∧
      scalarWidth P x = P.eps ∧ scalarMidpoint P x = nodeMidpoint P P.count
  objective_formula : ∀ p : EuclideanSpace ℝ (Fin 2),
    euclideanObjective P p =
      (scalarObjective P (p 0) + euclideanMovingProfile P p) / Real.sqrt 2
  nodal_gradients : ∀ k ≤ P.count,
    gradient (euclideanObjective P) (nodePoint P k) = nodeGradient P k ∧
      ‖gradient (euclideanObjective P) (nodePoint P k)‖ = cellLength P k
  prescribed_steps : ∀ k < P.count,
    nodePoint P (k + 1) = nodePoint P k - Real.sqrt 2 •
      gradient (euclideanObjective P) (nodePoint P k)

/-- Every admissible member of the actual finite family satisfies the source cell and
nodal data, with the explicitly documented exterior completion. -/
theorem finiteValleyData (P : Parameters) : FiniteValleyData P where
  length_formula k := by
    have hN : (P.count : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr P.count_pos)
    dsimp [cellLength]
    field_simp
  initial_point := by ext i; fin_cases i <;> simp [nodePoint, nodeX, nodeY]
  initial_value := by simp [nodeValue]
  node_recurrences k _ := ⟨nodeX_succ P k, nodeY_succ P k, nodeValue_succ P k⟩
  nodal_jets k hk j hj :=
    ⟨scalarObjective_node_jets P hk hj, scalarWidth_node_jets P hk hj,
      scalarMidpoint_node_jets P hk hj⟩
  objective_cells _ hk _ hx := scalarObjective_cell P hk hx
  width_cells _ hk _ hx := scalarWidth_cell P hk hx
  midpoint_cells _ hk _ hx := scalarMidpoint_cell P hk hx
  transverse_branches p := valley_profile_branches (scalarWidth_pos P (p 0)).le
  left_completion _ hx :=
    ⟨scalarObjective_left P hx, scalarWidth_left P hx, scalarMidpoint_left P hx⟩
  right_transition _ hx := scalarObjective_transition P hx
  right_completion x hx :=
    ⟨scalarObjective_right P hx, scalarWidth_right P (by linarith),
      scalarMidpoint_right P (by linarith)⟩
  objective_formula _ := rfl
  nodal_gradients _ hk := finite_valley_nodal_gradient P hk
  prescribed_steps _ hk := finite_valley_prescribed_step P hk

/-- Lemma B.2.2, with the finite index range and integer ceiling made explicit.
The function is the actual Hermite construction identified by `FiniteValleyData`;
it is globally C2 and its prescribed path first attains the gradient tolerance at N.
The constants for all scalar profiles and all moving-profile jets through order two
are uniform over the entire admissible finite family, independently of epsilon and N.
The exact displayed source count for integral reciprocal squares is recovered by
`lemma_B_2_2_integral_count`. -/
theorem lemma_B_2_2 (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    let P := roundedParameters eps hpos hle
    P.count = ⌈(eps ^ 2)⁻¹⌉₊ ∧ FiniteValleyData P ∧
      ContDiff ℝ 2 (euclideanObjective P) ∧
      ‖gradient (euclideanObjective P) (nodePoint P P.count)‖ = eps ∧
      (∀ k < P.count, eps < ‖gradient (euclideanObjective P) (nodePoint P k)‖) ∧
      (∃ C > 0, ∀ (Q : Parameters) (j : ℕ), j = 1 ∨ j = 2 → ∀ x : ℝ,
        |iteratedDeriv j (scalarObjective Q) x| ≤ 200 ∧
          |iteratedDeriv j (scalarWidth Q) x| ≤ C ∧
            |iteratedDeriv j (scalarMidpoint Q) x| ≤ C) ∧
      (∃ K > 0, ∀ (Q : Parameters) (j : ℕ), j ≤ 2 →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          ‖iteratedFDeriv ℝ j (euclideanMovingProfile Q) p‖ ≤ K) := by
  let P := roundedParameters eps hpos hle
  exact ⟨rfl, finiteValleyData P, finite_valley_c2 eps hpos hle,
    (finite_valley_first_tolerance P).1, (finite_valley_first_tolerance P).2,
    finite_valley_uniform_scalar_derivatives, finite_valley_uniform_mixed_derivatives⟩

/-- The exact reciprocal-square subfamily in Lemma B.2.2 has precisely the printed
integer count, without rounding, and the actual path first reaches tolerance there.
The supplied equality says only that the reciprocal square is integral; the result
still uses the concrete construction and its actual gradients. -/
theorem lemma_B_2_2_integral_count (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1)
    (N : ℕ) (hN : (eps ^ 2)⁻¹ = (N : ℝ)) :
    let P := roundedParameters eps hpos hle
    P.count = N ∧
      ‖gradient (euclideanObjective P) (nodePoint P N)‖ = eps ∧
        ∀ k < N, eps < ‖gradient (euclideanObjective P) (nodePoint P k)‖ := by
  have hc : (roundedParameters eps hpos hle).count = N := by
    simp only [roundedParameters_count, hN, Nat.ceil_natCast]
  refine ⟨hc, ?_, ?_⟩
  · simpa only [hc, roundedParameters_eps] using
      (finite_valley_first_tolerance (roundedParameters eps hpos hle)).1
  · simpa only [hc, roundedParameters_eps] using
      (finite_valley_first_tolerance (roundedParameters eps hpos hle)).2

/-- Lemma B.2.3 for the concrete finite family. A single constant bounds the actual
value and every genuine Fréchet derivative through order two of f2 on the entire
plane, hence on both moving unit strips in (B.2.19). Order zero includes the value;
order two includes both pure and mixed coordinate derivatives. The scalar width and
midpoint bounds account for all moving-coordinate chain terms. -/
theorem lemma_B_2_3 :
    (∃ K > 0, ∀ (P : Parameters) (j : ℕ), j ≤ 2 →
      ∀ p : EuclideanSpace ℝ (Fin 2),
        ‖iteratedFDeriv ℝ j (euclideanMovingProfile P) p‖ ≤ K ∧
          ∀ v : Fin j → EuclideanSpace ℝ (Fin 2), (∀ i, ‖v i‖ ≤ 1) →
            |iteratedFDeriv ℝ j (euclideanMovingProfile P) p v| ≤ K) ∧
    (∃ C > 0, ∀ (P : Parameters) (j : ℕ), j = 1 ∨ j = 2 → ∀ x : ℝ,
      |iteratedDeriv j (scalarWidth P) x| ≤ C ∧
        |iteratedDeriv j (scalarMidpoint P) x| ≤ C) :=
  by
  obtain ⟨K, hK, hb⟩ := finite_valley_uniform_mixed_derivatives
  refine ⟨⟨K, hK, fun P j hj p => ⟨hb P j hj p, ?_⟩⟩,
    exists_width_midpoint_derivative_bound⟩
  intro v hv
  have h := (iteratedFDeriv ℝ j (euclideanMovingProfile P) p).le_opNorm_mul_prod_of_le hv
  simp only [Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
  exact h.trans (hb P j hj p)

/-- Lemma B.2.4: the actual objective with the explicit bounded C2 right completion
has one global lower bound for all admissible finite parameters. -/
theorem lemma_B_2_4 (P : Parameters) (p : EuclideanSpace ℝ (Fin 2)) :
    -22 / Real.sqrt 2 ≤ euclideanObjective P p :=
  euclideanObjective_lower P p

/-- Lemma B.2.5: one positive constant, fixed before epsilon and N, makes every
actual finite objective's genuine gradient globally Lipschitz. All seams are C2.
The left extension is the affine source formula (B.2.24), not reflection in x. -/
theorem lemma_B_2_5 :
    (∀ P : Parameters, ContDiff ℝ 2 (euclideanObjective P)) ∧
      ∃ K : ℝ≥0, 0 < K ∧ ∀ P : Parameters,
        LipschitzWith K (gradient (euclideanObjective P)) :=
  ⟨contDiff_euclideanObjective, finite_valley_uniform_gradient_lipschitz⟩

/-- Lemma B.2.6 with the proof's explicit first-local-minimum meaning and its finite
index range. The successor is the actual negative-gradient step at sqrt2; it is a
genuine local minimum of the complete affine ray and every earlier nonnegative
parameter fails to be a local minimum. No global `LineSearch.IsExact` is asserted. -/
theorem lemma_B_2_6 (P : Parameters) {k : ℕ} (hk : k < P.count) :
    nodePoint P (k + 1) = nodePoint P k - Real.sqrt 2 •
      gradient (euclideanObjective P) (nodePoint P k) ∧
    IsLocalMin (fun a => euclideanObjective P
      (nodePoint P k - a • gradient (euclideanObjective P) (nodePoint P k))) (Real.sqrt 2) ∧
      ∀ a ∈ Ico (0 : ℝ) (Real.sqrt 2), ¬ IsLocalMin (fun a => euclideanObjective P
        (nodePoint P k - a • gradient (euclideanObjective P) (nodePoint P k))) a :=
  ⟨finite_valley_prescribed_step P hk, finite_valley_first_local_ray_minimum P hk⟩

end CartisGouldToint.AppendixB.Chapter02
