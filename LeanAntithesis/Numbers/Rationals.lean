import LeanAntithesis.Numbers.Integers
import LeanAntithesis.Logic.LinearTactic
import LeanAntithesis.Logic.AffineLint
import LeanAntithesis.Algebra.RingSolver
import LeanAntithesis.Algebra.OrderedRing

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

/-- Multiplication (numerators and denominators multiply). -/
protected def mul (a b : Frac) : Frac :=
  ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

instance : Add Frac := ⟨Frac.add⟩
instance : Neg Frac := ⟨Frac.neg⟩
instance : Sub Frac := ⟨Frac.sub⟩
instance : Mul Frac := ⟨Frac.mul⟩
instance : Zero Frac := ⟨0, 1, by omega⟩
instance : One Frac := ⟨1, 1, by omega⟩

/-! ### Projection lemmas — the operations are transparent, so these are `rfl`. -/

@[simp] theorem add_num (a b : Frac) : (a + b).num = a.num * b.den + b.num * a.den := rfl
@[simp] theorem add_den (a b : Frac) : (a + b).den = a.den * b.den := rfl
@[simp] theorem neg_num (a : Frac) : (-a).num = -a.num := rfl
@[simp] theorem neg_den (a : Frac) : (-a).den = a.den := rfl
@[simp] theorem mul_num (a b : Frac) : (a * b).num = a.num * b.num := rfl
@[simp] theorem mul_den (a b : Frac) : (a * b).den = a.den * b.den := rfl
@[simp] theorem zero_num : (0 : Frac).num = 0 := rfl
@[simp] theorem zero_den : (0 : Frac).den = 1 := rfl
@[simp] theorem one_num : (1 : Frac).num = 1 := rfl
@[simp] theorem one_den : (1 : Frac).den = 1 := rfl

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
  le_of_eq {a b} := @AOrd.le_of_eq ℤ _ (a.num * b.den) (b.num * a.den)

/-! ## The commutative ring structure

`Frac` equality is the integer cross-product equality, so every ring axiom is a valid
`ℤ` identity (discharged by `ring` after unfolding the transparent operations), and the
congruences are built from the forward cross-product implication (`cong₁`/`cong₂`,
mirroring `discrete.cong₂` but with the arithmetic of fractions). -/

/-- A `Frac` equality from the integer cross-product identity. -/
def rel_of_eq {a b : Frac} (h : a.num * b.den = b.num * a.den) : Valid (a ≈ₐ b) :=
  discrete.rel_of_eq h

/-- Unfold the transparent fraction operations and close the integer identity. -/
macro "frac_ring" : tactic =>
  `(tactic| (simp only [add_num, add_den, mul_num, mul_den, neg_num, neg_den,
    zero_num, zero_den, one_num, one_den]; ring))

/-! ### The congruences, *inside the calculus*

A `Frac` equality is a `ℤ` (discrete) equality of cross-products, so each congruence is the
**integer** congruence (`discrete.cong₁`/`discrete.cong₂` — these already handle the
apartness/refutation side once and for all) applied to the right linear/bilinear combination
of cross-products, then transported to the goal's cross-product form.  The transport is done
*on the sequent* in the proof mode (exactly the `aLE.trans` pattern): the two ring-rearrangement
equalities go in as `lhave` resources and compose through `AEquiv.trans` — no combinator takes
the equalities as parameters, and there is no hand-rolled evidence. -/

/-- Negation respects `≈`. -/
def negCong {a a' : Frac} : (a ≈ₐ a') ⊢ (-a ≈ₐ -a') := by
  linear
  lmap this (discrete.cong₁ (fun x : ℤ => -x))                 -- this : -X ≈ -Y
  lhave eL (show Valid ((-a).num * (-a').den ≈ₐ -(a.num * a'.den))
    by simp only [neg_num, neg_den]; aring)
  lhave eR (show Valid (-(a'.num * a.den) ≈ₐ (-a').num * (-a).den)
    by simp only [neg_num, neg_den]; aring)
  lcombine t₁ eL this (AEquiv.trans ..)
  lcombine t₂ t₁ eR (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- Addition respects `≈`: `(a+b)`'s cross-product is `(a.num·a'.den)·(b.den·b'.den)` plus
`(b.num·b'.den)·(a.den·a'.den)`, the bilinear combination of the two hypotheses. -/
def addCong {a a' b b' : Frac} : (a ≈ₐ a') ⊓ (b ≈ₐ b') ⊢ (a + b ≈ₐ a' + b') := by
  linear
  lmap this (discrete.cong₂ (fun x y : ℤ => x * (b.den * b'.den) + y * (a.den * a'.den)))
  lhave eL (show Valid ((a + b).num * (a' + b').den
      ≈ₐ a.num * a'.den * (b.den * b'.den) + b.num * b'.den * (a.den * a'.den))
    by simp only [add_num, add_den]; aring)
  lhave eR (show Valid (a'.num * a.den * (b.den * b'.den) + b'.num * b.den * (a.den * a'.den)
      ≈ₐ (a' + b').num * (a + b).den)
    by simp only [add_num, add_den]; aring)
  lcombine t₁ eL this (AEquiv.trans ..)
  lcombine t₂ t₁ eR (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- Multiplication respects `≈`: the product of the cross-products is the cross-product of
the product. -/
def mulCong {a a' b b' : Frac} : (a ≈ₐ a') ⊓ (b ≈ₐ b') ⊢ (a * b ≈ₐ a' * b') := by
  linear
  lmap this (discrete.cong₂ (fun x y : ℤ => x * y))
  lhave eL (show Valid ((a * b).num * (a' * b').den ≈ₐ a.num * a'.den * (b.num * b'.den))
    by simp only [mul_num, mul_den]; aring)
  lhave eR (show Valid (a'.num * a.den * (b'.num * b.den) ≈ₐ (a' * b').num * (a * b).den)
    by simp only [mul_num, mul_den]; aring)
  lcombine t₁ eL this (AEquiv.trans ..)
  lcombine t₂ t₁ eR (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- `Frac` is an **affine commutative ring**. -/
instance : ARing Frac where
  add_assoc a b c := rel_of_eq (by frac_ring)
  add_comm a b := rel_of_eq (by frac_ring)
  zero_add a := rel_of_eq (by frac_ring)
  neg_add_cancel a := rel_of_eq (by frac_ring)
  mul_assoc a b c := rel_of_eq (by frac_ring)
  mul_comm a b := rel_of_eq (by frac_ring)
  one_mul a := rel_of_eq (by frac_ring)
  left_distrib a b c := rel_of_eq (by frac_ring)
  add_cong' := addCong
  mul_cong' := mulCong
  neg_cong' := negCong

/-! ## Compatibility of the order with the ring structure

Each lemma scales the integer cross-products by the relevant (positive) denominators
via `intLE.mulRight`, combines them with the integer `add_le_add`, and transports the
endpoints to the goal's cross-product form with `intLE.ofEq` (the `ℤ` identities by
`ring`).  No `linarith`; the only Lean-level facts are positivity of denominators. -/

/-- Addition is monotone. -/
def aLE.add_le_add {a b c d : Frac} : (a ≤ₐ b) ⊗ (c ≤ₐ d) ⊢ (a + c ≤ₐ b + d) := by
  linear
  lintro hab hcd
  lhave pcd (intLE.nonneg (Int.mul_pos c.den_pos d.den_pos).le)
  lcombine s1 pcd hab intLE.mulRight
  lhave pab (intLE.nonneg (Int.mul_pos a.den_pos b.den_pos).le)
  lcombine s2 pab hcd intLE.mulRight
  lcombine t s1 s2 (AOrderedRing.add_le_add (α := ℤ))
  lmap t (intLE.ofEq (a' := (a + c).num * (b + d).den) (b' := (b + d).num * (a + c).den)
    (by simp only [add_num, add_den]; ring) (by simp only [add_num, add_den]; ring))
  lexact (Entails.refl _)

/-- Right multiplication by a nonnegative element is monotone. -/
def aLE.mul_le_mul_right {a b c : Frac} : (0 ≤ₐ c) ⊗ (a ≤ₐ b) ⊢ (a * c ≤ₐ b * c) := by
  linear
  lintro hc hab
  -- from `0 ≤ₐ c` (i.e. `0 ≤ c.num`), build `0 ≤ c.num * c.den` to scale by
  lhave pd (intLE.nonneg c.den_pos.le)
  lcombine s0 pd hc intLE.mulRight
  lmap s0 (intLE.ofEq (a' := (0 : ℤ)) (b' := c.num * c.den)
    (by simp only [zero_num]; ring) (by simp only [zero_den]; ring))
  lcombine s1 s0 hab intLE.mulRight
  lmap s1 (intLE.ofEq (a' := (a * c).num * (b * c).den) (b' := (b * c).num * (a * c).den)
    (by simp only [mul_num, mul_den]; ring) (by simp only [mul_num, mul_den]; ring))
  lexact (Entails.refl _)

/-- `Frac` is an **affine ordered commutative ring** — the carrier the `llinarith`
solver runs over, and (being a field of fractions) the one whose division will let
`llinarith` clear rational coefficients. -/
instance : AOrderedRing Frac where
  add_le_add := aLE.add_le_add
  mul_le_mul_right := aLE.mul_le_mul_right
  zero_le_one := intLE.nonneg (by simp only [zero_den, one_num]; omega)

end Frac
end Antithesis
