import LeanAntithesis.Sets.Equivalence

/-!
# Affine orders

An `AOrd α` is an `AProp`-valued order `≤ₐ` built on top of an affine equivalence
(`AOrd` **extends** `AEquiv`): reflexive, transitive, and **antisymmetric** — where
antisymmetry is what ties the order to the equivalence (`a ≤ b` and `b ≤ a` give
`a ≈ b`).

There is no separate strict-order operation: the strict order is the De Morgan dual
of the reverse order, `a <ₐ b := (b ≤ₐ a)ᗮ` (so `(a <ₐ b)⁺` is the *apartness witness*
that `b ≤ a` fails — a rational strictly between, etc.).
-/

universe u

namespace Antithesis
open scoped Antithesis

/-- A type carries an affine **order** valued in `AProp`, on top of its affine
equivalence. -/
class AOrd (α : Type u) extends AEquiv α where
  /-- The order; `(le a b)⁺` affirms `a ≤ b`. -/
  le : α → α → AProp.{u}
  /-- Reflexivity. -/
  le_refl : ∀ a, Valid (le a a)
  /-- Transitivity (multiplicative — composes via `cut`). -/
  le_trans : ∀ a b c, le a b ⊗ le b c ⊢ le a c
  /-- **Antisymmetry**: the order pinches down to the equivalence. -/
  le_antisymm : ∀ a b, le a b ⊗ le b a ⊢ rel a b
  /-- Equality **refines** the order (`a ≈ b ⊢ a ≤ b`) — so `≤ₐ` is a congruence for `≈ₐ`. -/
  le_of_eq : ∀ {a b}, rel a b ⊢ le a b

@[inherit_doc] scoped infix:50 " ≤ₐ " => AOrd.le

namespace AOrd
variable {α : Type u} [AOrd α]

/-- The **strict** order, derived as the antithesis of the reverse order:
`a <ₐ b := (b ≤ₐ a)ᗮ`.  Its affirmation is the refutation of `b ≤ a`. -/
def lt (a b : α) : AProp.{u} := (AOrd.le b a)ᗮ

/-- Transport the **left** endpoint of `≤ₐ` along a valid equality. -/
def le_congrL {a a' b : α} (h : Valid (a ≈ₐ a')) : (a ≤ₐ b) ⊢ (a' ≤ₐ b) :=
  have ea : Valid (a' ≤ₐ a) := cut (cut h (AEquiv.symm a a')) le_of_eq
  cut unit_tensor (cut tensor_comm (cut (tensor_mono ea (Entails.refl _)) (le_trans a' a b)))

/-- Transport the **right** endpoint of `≤ₐ` along a valid equality. -/
def le_congrR {a b b' : α} (h : Valid (b ≈ₐ b')) : (a ≤ₐ b) ⊢ (a ≤ₐ b') :=
  have eb : Valid (b ≤ₐ b') := cut h le_of_eq
  cut unit_tensor (cut (tensor_mono (Entails.refl _) eb) (le_trans a b b'))

/-- Transport both endpoints (the form `aring` feeds — ring-identity equalities). -/
def le_congr {a a' b b' : α} (ha : Valid (a ≈ₐ a')) (hb : Valid (b ≈ₐ b')) :
    (a ≤ₐ b) ⊢ (a' ≤ₐ b') :=
  cut (le_congrL ha) (le_congrR hb)

end AOrd

@[inherit_doc] scoped infix:50 " <ₐ " => AOrd.lt

end Antithesis
