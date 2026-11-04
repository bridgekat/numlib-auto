/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Preconditioned
import NumlibSurface.ConnGouldToint.Chapter04.Section04

/-! # Problems with linear constraints

The null-space and projected preconditioned conjugate-gradient methods of
Section 5.4 of [conn2000trust]. The backbone residual is the negative of the
textbook gradient.
-/

namespace ConnGouldToint.Chapter05

open Krylov
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Algorithm 5.4.2 uses the projected inverse N B N* in the original space,
where B is the inverse of the reduced preconditioner. -/
noncomputable abbrev projectedPCG (H : E →ₗ[ℝ] E) (N : F →L[ℝ] E) (B : F →ₗ[ℝ] F)
    (c : E) (u₀ : F) (k : ℕ) : PCG.State E :=
  PCG.iterate H (N.toLinearMap ∘ₗ B ∘ₗ N.adjoint.toLinearMap) (-c) (N u₀) k

/-- Algorithms 5.4.1 and 5.4.2 agree after mapping the reduced iterates and
directions by N, and mapping the full residual by N*. -/
theorem algorithm_5_4_2_eq_reduced (H : E →ₗ[ℝ] E) (N : F →L[ℝ] E) (B : F →ₗ[ℝ] F)
    (c : E) (u₀ : F) (k : ℕ) :
    let HN := N.adjoint.toLinearMap ∘ₗ H ∘ₗ N.toLinearMap
    let s := PCG.iterate HN B (-(N.adjoint c)) u₀ k
    let t := projectedPCG H N B c u₀ k
    t.x = N s.x ∧ N.adjoint t.r = s.r ∧ t.p = N s.p := by
  let HN := N.adjoint.toLinearMap ∘ₗ H ∘ₗ N.toLinearMap
  let P := N.toLinearMap ∘ₗ B ∘ₗ N.adjoint.toLinearMap
  let S := PCG.iterate HN B (-(N.adjoint c)) u₀
  let T := PCG.iterate H P (-c) (N u₀)
  change (T k).x = N (S k).x ∧ N.adjoint (T k).r = (S k).r ∧ (T k).p = N (S k).p
  have hp (z : E) : P z = N (B (N.adjoint z)) := rfl
  have hhn (z : F) : HN z = N.adjoint (H (N z)) := rfl
  have hn (z : E) : ⟪z, P z⟫ = ⟪N.adjoint z, B (N.adjoint z)⟫ := by
    rw [hp, N.adjoint_inner_left]
  induction k with
  | zero =>
    have hr : N.adjoint (T 0).r = (S 0).r := by
      change N.adjoint (-c - H (N u₀)) = -(N.adjoint c) - HN u₀
      rw [map_sub, map_neg, hhn]
    exact ⟨rfl, hr, by
      change P ((T 0).r) = N (B (S 0).r)
      rw [hp, hr]⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp'⟩ := ih
    have ha : PCG.alpha H P (T k) = PCG.alpha HN B (S k) := by
      rw [PCG.alpha, PCG.alpha, hn, hr, hp', hhn, N.adjoint_inner_left]
    have hr' : N.adjoint (T (k + 1)).r = (S (k + 1)).r := by
      simp only [T, S, PCG.iterate_succ, PCG.step_r]
      change N.adjoint ((T k).r - PCG.alpha H P (T k) • H (T k).p) =
        (S k).r - PCG.alpha HN B (S k) • HN (S k).p
      rw [map_sub, map_smul, ha, hr, hp', hhn]
    have ht : PCG.step H P (T k) = T (k + 1) := (PCG.iterate_succ H P (-c) (N u₀) k).symm
    have hs : PCG.step HN B (S k) = S (k + 1) :=
      (PCG.iterate_succ HN B (-(N.adjoint c)) u₀ k).symm
    have hb : PCG.beta H P (T k) = PCG.beta HN B (S k) := by
      simp only [PCG.beta, hn, ht, hs]
      change ⟪N.adjoint (T (k + 1)).r, B (N.adjoint (T (k + 1)).r)⟫ /
        ⟪N.adjoint (T k).r, B (N.adjoint (T k).r)⟫ =
        ⟪(S (k + 1)).r, B (S (k + 1)).r⟫ / ⟪(S k).r, B (S k).r⟫
      rw [hr', hr]
    refine ⟨?_, hr', ?_⟩
    · simp only [T, S, PCG.iterate_succ, PCG.step_x]
      change (T k).x + PCG.alpha H P (T k) • (T k).p =
        N ((S k).x + PCG.alpha HN B (S k) • (S k).p)
      rw [hx, ha, hp', map_add, map_smul]
    · rw [← ht, ← hs, PCG.step_p, PCG.step_p, ht, hs]
      change P (T (k + 1)).r + PCG.beta H P (T k) • (T k).p =
        N (B (S (k + 1)).r + PCG.beta HN B (S k) • (S k).p)
      rw [hp, hr', hb, hp', map_add, map_smul]

/-- The projected preconditioned residual is feasible and solves the saddle
system (5.4.5), provided the null-space map spans the kernel and the reduced
preconditioner is inverted by B. -/
theorem projected_inverse_5_4_5 {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y]
    (A : E →L[ℝ] Y) (N : F →L[ℝ] E) (M : E →ₗ[ℝ] E) (B : F →ₗ[ℝ] F)
    (hN : LinearMap.range N.toLinearMap = LinearMap.ker A.toLinearMap)
    (hB : ∀ z : F, N.adjoint (M (N (B z))) = z) (g : E) :
    let v := N (B (N.adjoint g))
    A v = 0 ∧ ∃ w : Y, M v + A.adjoint w = g := by
  intro v
  have hv : v ∈ LinearMap.range N.toLinearMap := ⟨B (N.adjoint g), rfl⟩
  rw [hN] at hv
  refine ⟨hv, ?_⟩
  have ho : g - M v ∈ (LinearMap.ker A.toLinearMap)ᗮ := by
    rw [← hN, Submodule.mem_orthogonal]
    rintro _ ⟨d, rfl⟩
    change ⟪N d, g - M v⟫ = 0
    rw [← N.adjoint_inner_right, map_sub]
    change ⟪d, N.adjoint g - N.adjoint (M (N (B (N.adjoint g))))⟫ = 0
    rw [hB, sub_self, inner_zero_right]
  rw [LinearMap.orthogonal_ker] at ho
  obtain ⟨w, hw⟩ := ho
  exact ⟨w, eq_sub_iff_add_eq'.mp hw⟩

/-- Shifting the right-hand side by a constraint adjoint preserves the
primal component and shifts the multiplier as in (5.4.7). -/
theorem shifted_projected_system_5_4_7 {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (A : E →L[ℝ] Y) (M : E →ₗ[ℝ] E) (g v : E) (u y : Y) :
    (A v = 0 ∧ M v + A.adjoint (y + u) = g) ↔
      (A v = 0 ∧ M v + A.adjoint u = g - A.adjoint y) := by
  rw [map_add, and_congr_right_iff]
  intro _
  rw [eq_sub_iff_add_eq]
  abel_nf


/-- Equations (5.4.1)–(5.4.2). The reduced objective equals the original
objective on the image of the null-space map. If that image is the kernel,
the unconstrained reduced minimizers yield exactly the feasible minimizers. -/
theorem null_space_quadratic_5_4_2 {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (A : E →ₗ[ℝ] Y) (H : E →ₗ[ℝ] E) (N : F →L[ℝ] E) (c : E)
    (hN : LinearMap.range N.toLinearMap = LinearMap.ker A) (u : F) :
    let q (x : E) := (1 / 2 : ℝ) * ⟪x, H x⟫ + ⟪c, x⟫
    let qN (z : F) := (1 / 2 : ℝ) * ⟪z, N.adjoint (H (N z))⟫ + ⟪N.adjoint c, z⟫
    q (N u) = qN u ∧ (IsMinOn qN Set.univ u ↔ IsMinOn q (LinearMap.ker A) (N u)) := by
  intro q qN
  have hq (z : F) : q (N z) = qN z := by
    change (1 / 2 : ℝ) * ⟪N z, H (N z)⟫ + ⟪c, N z⟫ =
      (1 / 2 : ℝ) * ⟪z, N.adjoint (H (N z))⟫ + ⟪N.adjoint c, z⟫
    rw [N.adjoint_inner_right, N.adjoint_inner_left]
  refine ⟨hq u, ?_⟩
  constructor
  · intro h x hx
    rw [← hN] at hx
    obtain ⟨z, rfl⟩ := hx
    change q (N u) ≤ q (N z)
    rw [hq, hq]
    exact h (Set.mem_univ z)
  · intro h z _
    have hz : N z ∈ LinearMap.ker A := hN ▸ ⟨z, rfl⟩
    change qN u ≤ qN z
    rw [← hq, ← hq]
    exact h hz

/-- The projected iterates, search directions, and preconditioned residuals
stay in the null space of the constraint operator. -/
theorem projectedPCG_feasible {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (A : E →ₗ[ℝ] Y) (H : E →ₗ[ℝ] E) (N : F →L[ℝ] E) (B : F →ₗ[ℝ] F)
    (hN : ∀ u, A (N u) = 0) (c : E) (u₀ : F) (k : ℕ) :
    let t := projectedPCG H N B c u₀ k
    A t.x = 0 ∧ A t.p = 0 ∧ A (N (B (N.adjoint t.r))) = 0 := by
  intro t
  obtain ⟨hx, _, hp⟩ := algorithm_5_4_2_eq_reduced H N B c u₀ k
  exact ⟨hx ▸ hN _, hp ▸ hN _, hN _⟩

open scoped Matrix

/-- A minimizer of the homogeneous equality-constrained quadratic satisfies
the augmented system (5.4.6). -/
theorem constrained_quadratic_system_5_4_6 {m n : ℕ}
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (c x : Fin n → ℝ)
    (hmin : Chapter04.IsEqualityQuadraticMin H A (-c) x 0) :
    ∃ y : Fin m → ℝ, Matrix.saddleMatrix H Aᵀ 0 *ᵥ Sum.elim x (-y) = Sum.elim (-c) 0 := by
  obtain ⟨hx, ⟨y, hy⟩, _⟩ := (Chapter04.quadratic_minimum_4_4_14_iff hH A (-c) x 0).mp hmin
  exact ⟨y, (Chapter04.projection_system_4_4_8 H A x (-c) y 0).mpr ⟨hy, hx⟩⟩

end ConnGouldToint.Chapter05
