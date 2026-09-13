import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section05

/-!
# Quarteroni–Sacco–Saleri §2.6: exercises

Surface file for the two exercises of [quarteroni2000numerical] §2.6 that the main text cites:
Exercise 11, which proves (2.37), and Exercise 12, the quantitative form of the failure of
associativity of `⊕`. Both are `Numlib/FloatingPoint/System.lean` statements read over `ℝ` through
the machine sum `machineOp s (· + ·)` of `Chapter02/Section05`, with the book's `≃` bounds made
exact by keeping the second-order terms. The remaining exercises are not cited by the text and are
not nodes.
-/

open FloatingPoint

namespace QuarteroniSaccoSaleri.Chapter02

/-- **Exercise 11**, i.e. **(2.37)**: for `x + y ≠ 0`,

`|x ⊕ y - (x + y)| / |x + y| ≤ u (1 + u) (|x| + |y|) / |x + y| + u`.

The book states it "for all `x, y ∈ 𝔽`", where `fl(x) = x` and the bound is weaker than (2.36);
it holds, by the book's own hint — split off `fl(x) + fl(y)` and use (2.36) and (2.35) — for
arbitrary real operands, which is how it is stated. -/
theorem exercise_2_11 (s : System) {x y : ℝ} (hxy : x + y ≠ 0) :
    |machineOp s (· + ·) x y - (x + y)| / |x + y| ≤
      s.unitRoundoff ℝ * (1 + s.unitRoundoff ℝ) * (|x| + |y|) / |x + y| + s.unitRoundoff ℝ := by
  have hpos : 0 < |x + y| := abs_pos.2 hxy
  rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne']
  exact s.abs_add_sub_le x y

/-- **Exercise 12, first bound**: for `x, y, z ∈ 𝔽`,
`|(x ⊕ y) ⊕ z - (x + y + z)| ≤ C₁ = (2 |x + y| + |z|) u + |x + y| u²`; the book's `C₁ ≃ (2|x + y| +
|z|) u` drops the `u²` term. The book's hypothesis that `x + y`, `y + z`, `x + y + z` "fall into the
range of `𝔽`" is not needed for the bound, Property 2.1 being unconditional in the backbone; it
would be needed for the intermediate results to lie in `𝔽`. -/
theorem exercise_2_12_left (s : System) {x y z : ℝ} (hx : x ∈ s.numbers ℝ) (hy : y ∈ s.numbers ℝ)
    (hz : z ∈ s.numbers ℝ) :
    |machineOp s (· + ·) (machineOp s (· + ·) x y) z - (x + y + z)| ≤
      (2 * |x + y| + |z|) * s.unitRoundoff ℝ + |x + y| * s.unitRoundoff ℝ ^ 2 :=
  s.abs_add_add_sub_le hx hy hz

/-- **Exercise 12, second bound**: for `x, y, z ∈ 𝔽`,
`|x ⊕ (y ⊕ z) - (x + y + z)| ≤ C₂ = (|x| + 2 |y + z|) u + |y + z| u²`; the book's `C₂ ≃ (|x| + 2|y +
z|) u`. It is the first bound with the roles of `x` and `y + z` exchanged, by commutativity of
`⊕`. -/
theorem exercise_2_12_right (s : System) {x y z : ℝ} (hx : x ∈ s.numbers ℝ) (hy : y ∈ s.numbers ℝ)
    (hz : z ∈ s.numbers ℝ) :
    |machineOp s (· + ·) x (machineOp s (· + ·) y z) - (x + y + z)| ≤
      (|x| + 2 * |y + z|) * s.unitRoundoff ℝ + |y + z| * s.unitRoundoff ℝ ^ 2 :=
  s.abs_add_add_sub_le' hx hy hz

end QuarteroniSaccoSaleri.Chapter02
