import LeanAntithesis.Algebra.LinarithSolver
import LeanAntithesis.Numbers.Integers
import LeanAntithesis.Numbers.Rationals

/-! Tests for the affine `llinarith` solver over `ℤ` and `Frac` (both `AOrderedRing`). -/

namespace Antithesis
open scoped Antithesis

-- transitivity (certificate λ = (1,1))
example {a b c : ℤ} : (a ≤ₐ b) ⊗ (b ≤ₐ c) ⊢ (a ≤ₐ c) := by
  linear
  lintro h1 h2
  llinarith

-- a single hypothesis, used directly
example {a b : ℤ} : (a ≤ₐ b) ⊢ (a ≤ₐ b) := by
  linear
  lintro h
  llinarith

-- a four-step chain
example {a b c d e : ℤ} :
    (a ≤ₐ b) ⊗ ((b ≤ₐ c) ⊗ ((c ≤ₐ d) ⊗ (d ≤ₐ e))) ⊢ (a ≤ₐ e) := by
  linear
  lintro h1 rest; lswap; lintro h2 rest2; lswap; lintro h3 h4
  llinarith

-- an irrelevant hypothesis is discarded
example {a b c x y : ℤ} : (a ≤ₐ b) ⊗ ((x ≤ₐ y) ⊗ (b ≤ₐ c)) ⊢ (a ≤ₐ c) := by
  linear
  lintro h1 rest; lswap; lintro hxy h2
  llinarith

-- combining additive facts: `a ≤ b` and `c ≤ d` give `a + c ≤ b + d`
example {a b c d : ℤ} : (a + c ≤ₐ b) ⊗ (b ≤ₐ d) ⊢ (a + c ≤ₐ d) := by
  linear
  lintro h1 h2
  llinarith

/-! ### General coefficients (v2) -/

-- coefficient 2: scaling a single hypothesis
example {a b : ℤ} : (a ≤ₐ b) ⊢ (2 * a ≤ₐ 2 * b) := by
  linear
  lintro h
  llinarith

-- coefficient 3
example {a b : ℤ} : (a ≤ₐ b) ⊢ (3 * a ≤ₐ 3 * b) := by
  linear
  lintro h
  llinarith

-- scaled transitivity: λ = (2, 2)
example {a b c : ℤ} : (a ≤ₐ b) ⊗ (b ≤ₐ c) ⊢ (2 * a ≤ₐ 2 * c) := by
  linear
  lintro h1 h2
  llinarith

/-! ### Constant slack (v2) -/

-- pure constant slack, no hypotheses
example : Valid ((2 : ℤ) ≤ₐ 5) := by
  linear
  llinarith

-- one hypothesis plus a constant
example {a b : ℤ} : (a ≤ₐ b) ⊢ (a ≤ₐ b + 3) := by
  linear
  lintro h
  llinarith

-- coefficients and slack together: λ = (2, 2), s = 1
example {a b c : ℤ} : (a ≤ₐ b) ⊗ (b ≤ₐ c) ⊢ (2 * a ≤ₐ 2 * c + 1) := by
  linear
  lintro h1 h2
  llinarith

-- an equality goal that follows by ring rearrangement alone (empty certificate)
example {a b : ℤ} : Valid (a + b ≤ₐ b + a) := by
  linear
  llinarith

/-! ### Over `Frac` (the rational carrier — also an `AOrderedRing`) -/

example {a b c : Frac} : (a ≤ₐ b) ⊗ (b ≤ₐ c) ⊢ (a ≤ₐ c) := by
  linear; lintro h1 h2; llinarith

example {a b c d : Frac} : (a ≤ₐ b) ⊗ (c ≤ₐ d) ⊢ (a + c ≤ₐ b + d) := by
  linear; lintro h1 h2; llinarith

-- constant slack over `Frac`
example {a b : Frac} : (a ≤ₐ b) ⊢ (a ≤ₐ b + 1) := by
  linear; lintro h; llinarith

end Antithesis
