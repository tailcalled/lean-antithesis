import LeanAntithesis.Algebra.OrderedRing
import LeanAntithesis.Sets.AffineRw
import LeanAntithesis.Numbers.Integers

/-! Tests for the **persistent zone**: duplicable (`!`-)resources in the `linear` proof mode.

A `!P` resource is reusable.  `ldup`/`lcopy` make copies; the combinators (`lmap`/`lcombine`)
auto-derelict a `!P` argument when the underlying `P` is wanted; and the closing tactics
(`lexact`/`lclose`) discard any leftover `!`-resources automatically. -/

namespace Antithesis
open scoped Antithesis

/-- `lcombine` auto-derelicts the duplicable `ha : !(0 ≤ₐ a)` — no explicit `derelict`/`ldup`. -/
example {a b : ℤ} : ！(0 ≤ₐ a) ⊗ (0 ≤ₐ b) ⊢ (0 ≤ₐ a + b) := by
  linear
  lintro ha hb
  lcombine s ha hb AOrderedRing.add_nonneg
  lexact (Entails.refl _)

/-- A leftover `!`-resource is discarded automatically at `lexact`. -/
example {a : ℤ} {P : AProp} : ！(0 ≤ₐ a) ⊗ P ⊢ P := by
  linear
  lintro hbang hp
  lexact (Entails.refl _)

/-- Reuse: the duplicable `this` is used three times — copied twice with `ldup`, then
auto-derelicted by the final `lcombine` — and the persistent original is dropped on close. -/
example {a : ℤ} : ！(0 ≤ₐ a) ⊢ (0 ≤ₐ a + a + a) := by
  linear
  ldup this h1
  ldup this h2
  lcombine s1 h1 h2 AOrderedRing.add_nonneg     -- 0 ≤ₐ a + a
  lcombine s2 s1 this AOrderedRing.add_nonneg   -- `this` auto-derelicts; 0 ≤ₐ (a + a) + a
  lexact (Entails.refl _)

/-- `lcopy` makes a `!`-copy (keeping the original); here both copies feed one `lcombine`,
which auto-derelicts each. -/
example {a : ℤ} : ！(0 ≤ₐ a) ⊢ (0 ≤ₐ a + a) := by
  linear
  lcopy this hc
  lcombine s this hc AOrderedRing.add_nonneg
  lexact (Entails.refl _)

/-! ### `arw` rewriting by context resources -/

/-- `arw` rewrites the goal by a **linear** context equality, consuming it. -/
example {a x y : ℤ} : (x ≈ₐ y) ⊢ (x + a ≈ₐ y + a) := by
  linear; lintro h; arw [h]

/-- `arw` rewrites by a **duplicable** (`!`-)context equality — a copy is taken (so the
resource persists, discarded only at the close), and both occurrences of `x` are rewritten. -/
example {x y : ℤ} : ！(x ≈ₐ y) ⊢ (x + x ≈ₐ y + y) := by
  linear; lintro h; arw [h]

/-- A duplicable context equality is genuinely reused: `arw [h]` in *both* branches of the
`⊓` (the resource is shared additively and persists through each rewrite). -/
example {x y : ℤ} : ！(x ≈ₐ y) ⊢ ((x ≈ₐ y) ⊓ (x ≈ₐ y)) := by
  linear
  lintro h
  lwith
  · arw [h]
  · arw [h]

end Antithesis
