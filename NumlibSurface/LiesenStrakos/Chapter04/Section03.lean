import Numlib.Krylov.ShortRecurrence
import NumlibSurface.LiesenStrakos.Chapter04.Section02

/-!
# Liesen and Strakoš, Section 4.3: Optimal short recurrences

Section 4.3 of [liesen2013krylov] characterizes the length of an Arnoldi recurrence
by the bandwidth of its rectangular unreduced Hessenberg matrix. The orthonormal
Arnoldi basis from `Numlib.Krylov.Arnoldi` has the same zero pattern in its coefficient
matrix as the orthogonal basis.

## Main definitions

* Definition 4.3.1, `LiesenStrakos.IsBandHessenberg`: unreduced Hessenberg with exact
  upper bandwidth $s$.
* Definition 4.3.3 (1), `LiesenStrakos.AdmitsOptimalRecurrenceFor`: an optimal $(s+2)$-term
  Arnoldi recurrence for one starting vector.
* Definition 4.3.3 (2), `LiesenStrakos.AdmitsOptimalRecurrence`: optimal recurrence length
  at most $s+2$ for all starts and exactly $s+2$ for some start.

## Main results

* Remark 4.3.2, `LiesenStrakos.remark_4_3_2`: the rectangular isometry transports a companion
  matrix and its down-shift recurrence.

## Deviations from the source

* **Definitions 4.3.1 and 4.3.3** (generalization). The Hessenberg predicate is scalar
  generic, and the recurrence predicates also apply over the reals. See
  `LiesenStrakos.IsBandHessenberg`, `LiesenStrakos.AdmitsOptimalRecurrenceFor` and
  `LiesenStrakos.AdmitsOptimalRecurrence`.
* **Remark 4.3.2** (correction). The rank of the constructed matrix is full on the column space
  only when the companion matrix is invertible.
-/

namespace LiesenStrakos

/-- A rectangular matrix $H$ of size $(m+1)\times m$ is $(s+2)$-band Hessenberg when its
subdiagonal has no zero entries, its entries below that subdiagonal or above the $s$-th
superdiagonal vanish, and the $s$-th superdiagonal contains a nonzero entry.
This is Definition 4.3.1 of [liesen2013krylov].

**Generalization.** The source uses complex matrices. The zero-pattern criterion
requires only a distinguished zero for the entries. -/
def IsBandHessenberg {𝕜 : Type*} [Zero 𝕜] {m : ℕ} (H : Matrix (Fin (m + 1)) (Fin m) 𝕜)
    (s : ℕ) : Prop :=
  H.IsUpperHessenbergRect ∧ (∀ j : Fin m, H j.succ j ≠ 0) ∧ H.HasUpperBandwidthRect s ∧
    ∃ (i : Fin (m + 1)) (j : Fin m), (j : ℕ) = i + s ∧ H i j ≠ 0

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a start $v$ of grade $d$, the operator admits an optimal $(s+2)$-term recurrence if
the $d\times(d-1)$ Arnoldi matrix has exact upper bandwidth $s$ and is unreduced.
The definition assumes $s+2\le d_{\min}(A)$. This is Definition 4.3.3 (1) of [liesen2013krylov].

**Generalization.** The source treats complex inner product spaces. The Arnoldi
bandwidth predicate also applies to real inner product spaces. -/
def AdmitsOptimalRecurrenceFor (A : Module.End 𝕜 E) (v : E) (s : ℕ) : Prop :=
  s + 2 ≤ operatorMinimalDegree A ∧
    IsBandHessenberg (Arnoldi.hessenberg A v (vectorGrade A v - 1)) s

/-- An operator admits an optimal $(s+2)$-term recurrence if all its pre-breakdown rectangular
Arnoldi matrices have upper bandwidth at most $s$, and there is a start giving exact upper
bandwidth $s$. This is Definition 4.3.3 (2) of [liesen2013krylov].

**Generalization.** The same two conditions define admissibility over the reals. -/
def AdmitsOptimalRecurrence (A : Module.End 𝕜 E) (s : ℕ) : Prop :=
  (∀ v : E, Arnoldi.HasUpperBandwidth A v s) ∧
    ∃ v : E, AdmitsOptimalRecurrenceFor A v s

open scoped Matrix

/-- Let $V$ have $d+1$ orthonormal columns and let $C$ have the down-shift columns of a companion
matrix through its first $d$ columns. Then $A=VCV^H$ satisfies $AV=VC$ and $V^H AV=C$, and applying
$A$ to each of the first $d$ columns of $V$ gives the next column. This is the construction in
Remark 4.3.2 of [liesen2013krylov].

**Correction.** The source claims full rank for every companion. Full rank on the column
space requires invertibility of $C$. For instance, $V=I$ and a companion with zero last
column give a singular $A$ for which the down-shift recurrence holds. -/
theorem remark_4_3_2 {n : Type*} [Fintype n] {d : ℕ}
    (V : Matrix n (Fin (d + 1)) ℂ) (C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hV : Vᴴ * V = 1) (hC : ∀ j : Fin d, C.col j.castSucc = Pi.single j.succ 1) :
    let A := V * C * Vᴴ
    A * V = V * C ∧ Vᴴ * A * V = C ∧
      ∀ j : Fin d, A *ᵥ V.col j.castSucc = V.col j.succ := by
  let A := V * C * Vᴴ
  have hAV : A * V = V * C := by
    simp only [A, Matrix.mul_assoc, hV, mul_one]
  refine ⟨hAV, ?_, fun j => ?_⟩
  · rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc, hV, one_mul]
  · rw [← Matrix.col_mul_eq_mulVec_col, hAV, Matrix.col_mul_eq_mulVec_col, hC,
      Matrix.mulVec_single_one]

end LiesenStrakos
