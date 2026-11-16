/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section05

/-!
# Quarteroni, Sacco and Saleri, Section 2.6: Exercises

This module formalizes the two exercises of Section 2.6 of [quarteroni2000numerical] that the main
text cites: Exercise 11, which proves the bound (2.37) on the relative error of the machine sum
$x \oplus y$, and Exercise 12, which bounds the errors of $(x \oplus y) \oplus z$ and
$x \oplus (y \oplus z)$ and so quantifies the failure of associativity of $\oplus$. Both are results
of the backbone module `Numlib.FloatingPoint.System`, read over $\mathbb{R}$ through the machine sum
`QuarteroniSaccoSaleri.Chapter02.machineOp s (· + ·)` of
`NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section05`. The bounds that the book writes with
$\simeq$ are made exact by keeping the second-order terms.

## Main results

* Exercise 11, `QuarteroniSaccoSaleri.Chapter02.exercise_2_11`: the bound (2.37), $|x \oplus y -
  (x + y)| / |x + y| \le u (1 + u)(|x| + |y|) / |x + y| + u$.
* Exercise 12, `QuarteroniSaccoSaleri.Chapter02.exercise_2_12_left`: $|(x \oplus y) \oplus z - (x +
  y + z)| \le (2 |x + y| + |z|) u + |x + y| u^2$.
* Exercise 12, `QuarteroniSaccoSaleri.Chapter02.exercise_2_12_right`: $|x \oplus (y \oplus z) - (x +
  y + z)| \le (|x| + 2 |y + z|) u + |y + z| u^2$.

## Deviations from the source

* **Exercise 11** (generalization). The book states (2.37) for $x, y \in \mathbb{F}$. The statement
  holds for all real $x, y$. See `QuarteroniSaccoSaleri.Chapter02.exercise_2_11`.
* **Exercise 12, the constants** (reading). The book writes $C_1$ and $C_2$ with $\simeq$ and drops
  the terms in $u^2$. The statements keep them. See
  `QuarteroniSaccoSaleri.Chapter02.exercise_2_12_left`.
* **Exercise 12, the range hypothesis** (generalization). The book assumes that $x + y$, $y + z$ and
  $x + y + z$ lie in the range of $\mathbb{F}$. The bounds hold without this hypothesis. See
  `QuarteroniSaccoSaleri.Chapter02.exercise_2_12_left`.

## Not formalized

* **The other exercises of Section 2.6.** The main text does not cite them.
-/

open FloatingPoint

namespace QuarteroniSaccoSaleri.Chapter02

/-- **Exercise 11** of Section 2.6 of [quarteroni2000numerical], equation (2.37). Let $\mathbb{F}$
be a floating-point system with roundoff unit $u$, and let $x, y \in \mathbb{R}$ with
$x + y \neq 0$. Then
$$\frac{|x \oplus y - (x + y)|}{|x + y|} \le u (1 + u) \frac{|x| + |y|}{|x + y|} + u.$$

**Generalization.** The book states the bound "for all $x, y \in \mathbb{F}$", where $fl(x) = x$
and the bound is weaker than (2.36). It holds for arbitrary real operands, by the hint of the
book (split off $fl(x) + fl(y)$ and use (2.36) and (2.35)), and it is stated so.

The machine sum $x \oplus y = fl(fl(x) + fl(y))$ is `QuarteroniSaccoSaleri.Chapter02.machineOp s
(· + ·) x y`, and $u$ is `FloatingPoint.System.unitRoundoff`. -/
theorem exercise_2_11 (s : System) {x y : ℝ} (hxy : x + y ≠ 0) :
    |machineOp s (· + ·) x y - (x + y)| / |x + y| ≤
      s.unitRoundoff ℝ * (1 + s.unitRoundoff ℝ) * (|x| + |y|) / |x + y| + s.unitRoundoff ℝ := by
  have hpos : 0 < |x + y| := abs_pos.2 hxy
  rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne']
  exact s.abs_add_sub_le x y

/-- **Exercise 12** of Section 2.6 of [quarteroni2000numerical], the first bound. Let $\mathbb{F}$
be a floating-point system with roundoff unit $u$, and let $x, y, z \in \mathbb{F}$. Then
$$|(x \oplus y) \oplus z - (x + y + z)| \le C_1 = (2 |x + y| + |z|) u + |x + y| u^2.$$

**Reading.** The book writes $C_1 \simeq (2 |x + y| + |z|) u$, which drops the term
$|x + y| u^2$. The statement keeps it.

**Generalization.** The book assumes that $x + y$, $y + z$ and $x + y + z$ "fall into the range
of $\mathbb{F}$". The bound does not need this hypothesis, because Property 2.1 holds without a
range hypothesis in the backbone. The hypothesis would be needed for the intermediate results to
lie in $\mathbb{F}$. -/
theorem exercise_2_12_left (s : System) {x y z : ℝ} (hx : x ∈ s.numbers ℝ) (hy : y ∈ s.numbers ℝ)
    (hz : z ∈ s.numbers ℝ) :
    |machineOp s (· + ·) (machineOp s (· + ·) x y) z - (x + y + z)| ≤
      (2 * |x + y| + |z|) * s.unitRoundoff ℝ + |x + y| * s.unitRoundoff ℝ ^ 2 :=
  s.abs_add_add_sub_le hx hy hz

/-- **Exercise 12** of Section 2.6 of [quarteroni2000numerical], the second bound. Let $\mathbb{F}$
be a floating-point system with roundoff unit $u$, and let $x, y, z \in \mathbb{F}$. Then
$$|x \oplus (y \oplus z) - (x + y + z)| \le C_2 = (|x| + 2 |y + z|) u + |y + z| u^2.$$

**Reading.** The book writes $C_2 \simeq (|x| + 2 |y + z|) u$, which drops the term
$|y + z| u^2$. The statement keeps it.

**Generalization.** As for the first bound, the range hypothesis of the book is not needed.

This is the first bound with the roles of $x$ and $y + z$ exchanged, by the commutativity of
$\oplus$. -/
theorem exercise_2_12_right (s : System) {x y z : ℝ} (hx : x ∈ s.numbers ℝ) (hy : y ∈ s.numbers ℝ)
    (hz : z ∈ s.numbers ℝ) :
    |machineOp s (· + ·) x (machineOp s (· + ·) y z) - (x + y + z)| ≤
      (|x| + 2 * |y + z|) * s.unitRoundoff ℝ + |y + z| * s.unitRoundoff ℝ ^ 2 :=
  s.abs_add_add_sub_le' hx hy hz

end QuarteroniSaccoSaleri.Chapter02
