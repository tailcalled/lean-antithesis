import LeanAntithesis.Numbers.Integers
import LeanAntithesis.Logic.LinearTactic
import LeanAntithesis.Algebra.RingSolver

/-!
# Rationals, inside the affine calculus

A rational is a **transparent fraction** `Frac` (numerator over a positive
denominator, not reduced).  Its order lives *in the antithesis calculus*: `aLE a b`
is an `AProp` whose affirmation is `a ≤ b` and whose refutation (apartness side) is
the strict reversal `b < a`.  The order laws are **sequents** built from the
calculus — reflexivity is `Valid`, transitivity is the multiplicative `⊗ ⊢`
(composing via `cut`).

The whole development reduces to the affine order on `ℤ` (`intLE`, from
`Integers.lean`): rationals compare by cross-multiplication, and every step is a
calculus combinator (`cut`, `tensor_mono`, `intLE.mulRight`/`cancelMul`/`trans`/
`ofEq`).  Only the atomic integer *identities* are discharged in plain Lean (`ring`),
and `Int` order is axiom-pure — so the rational order is `Classical`-free.
-/

namespace Antithesis
open scoped Antithesis

/-- A transparent rational: numerator over a positive denominator, **not** reduced. -/
structure Frac where
  /-- Numerator. -/
  num : Int
  /-- Denominator. -/
  den : Int
  /-- The denominator is positive. -/
  den_pos : 0 < den

namespace Frac

/-! ## Arithmetic — transparent, so it reduces to `Int` -/

/-- Addition (common denominator `a.den * b.den`). -/
protected def add (a b : Frac) : Frac :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩
/-- Negation. -/
protected def neg (a : Frac) : Frac := ⟨-a.num, a.den, a.den_pos⟩
/-- Subtraction. -/
protected def sub (a b : Frac) : Frac := a.add b.neg
/-- Absolute value. -/
protected def abs (a : Frac) : Frac := ⟨|a.num|, a.den, a.den_pos⟩

instance : Add Frac := ⟨Frac.add⟩
instance : Neg Frac := ⟨Frac.neg⟩
instance : Sub Frac := ⟨Frac.sub⟩

/-! ## Order, in the affine calculus

`aLE a b` reduces the rational order to the affine integer order `intLE` on the
cross-products `a.num * b.den` and `b.num * a.den`.  Its refutation is the strict
reversal, so apartness of rationals comes for free as `(aLE a b)ᗮ`. -/

/-- Affine order on rationals (affirmation `a ≤ b`, refutation `b < a`). -/
def aLE (a b : Frac) : AProp.{0} := intLE (a.num * b.den) (b.num * a.den)

/-- Reflexivity. -/
def aLE.refl (a : Frac) : Valid (aLE a a) := intLE.refl _

/-- Transitivity, **entirely on the sequent**: every fact — both denominators' (strict)
positivities and every cross-product rearrangement — enters as a resource (`lhave`) and is
consumed by a binary entailment (`lcombine`).  Scale each side by the other denominator
(`intLE.mulRight`), align/transport the cross-products along affine ℤ equalities
(`intLE.congrR`/`congrL`, with the `≈`-facts supplied by `aring`), chain with `intLE.trans`,
and cancel the common positive factor (`intLE.cancelMul`).  No combinator takes an
entailment as a *parameter*. -/
def aLE.trans {a b c : Frac} : aLE a b ⊗ aLE b c ⊢ aLE a c := by
  linear
  lintro hab hbc
  -- scale: hab by c.den, hbc by a.den (positivity on the sequent)
  lhave pc (intLE.nonneg (Int.le_of_lt c.den_pos))
  lcombine sab pc hab intLE.mulRight
  lhave pa (intLE.nonneg (Int.le_of_lt a.den_pos))
  lcombine sbc pa hbc intLE.mulRight
  -- align the shared middle term, then transitivity
  lhave em (show Valid (b.num * a.den * c.den ≈ₐ b.num * c.den * a.den) by aring)
  lcombine sab' em sab intLE.congrR
  lcombine t sab' sbc intLE.trans
  -- refactor both endpoints into `· * b.den` form, then cancel `b.den`
  lhave el (show Valid (a.num * b.den * c.den ≈ₐ a.num * c.den * b.den) by aring)
  lcombine t1 el t intLE.congrL
  lhave er (show Valid (c.num * b.den * a.den ≈ₐ c.num * a.den * b.den) by aring)
  lcombine t2 er t1 intLE.congrR
  lhave pb (intLE.gt_zero b.den_pos)
  lcombine r pb t2 intLE.cancelMul
  lexact (Entails.refl _)

/-- Transitivity of rational equality: the cross-products chain by cancelling the
middle denominator (which is positive, hence nonzero). -/
theorem crossEq_trans {a b c : Frac}
    (h₁ : a.num * b.den = b.num * a.den) (h₂ : b.num * c.den = c.num * b.den) :
    a.num * c.den = c.num * a.den :=
  mul_right_cancel₀ b.den_pos.ne' <| calc
    a.num * c.den * b.den = a.num * b.den * c.den := by ring
    _ = b.num * a.den * c.den := by rw [h₁]
    _ = b.num * c.den * a.den := by ring
    _ = c.num * b.den * a.den := by rw [h₂]
    _ = c.num * a.den * b.den := by ring

/-- `Frac` is an affine **order** (hence affine equivalence).  `≤ₐ` is `aLE`; equality
`≈ₐ` is resolved **directly** as equality of the integer cross-products `(a.num*b.den) ≈ₐ
(b.num*a.den)` (not `aLE`-both-ways).  Antisymmetry is then exactly the integer
antisymmetry on the cross-products, and `<ₐ`/apartness come for free as De Morgan duals. -/
instance : AOrd Frac where
  rel a b := a.num * b.den ≈ₐ b.num * a.den
  refl a := AEquiv.refl (a.num * a.den)
  symm a b := AEquiv.symm (a.num * b.den) (b.num * a.den)
  trans _ _ _ := AProp.ofTypes_tensor
    (fun h₁ h₂ => ⟨crossEq_trans h₁.down h₂.down⟩)
    (fun h₁ hz => ⟨fun h₂ => hz.down (crossEq_trans h₁.down h₂)⟩)
    (fun h₂ hz => ⟨fun h₁ => hz.down (crossEq_trans h₁ h₂.down)⟩)
  le := aLE
  le_refl := aLE.refl
  le_trans _ _ _ := aLE.trans
  le_antisymm a b := AOrd.le_antisymm (a.num * b.den) (b.num * a.den)

end Frac
end Antithesis
