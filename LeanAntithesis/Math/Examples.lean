import LeanAntithesis.Logic.Tactic
import LeanAntithesis.Logic.Calculus
import LeanAntithesis.Logic.Syntax

/-!
# Examples (Type-valued)

Surface syntax, and Shulman's headline phenomenon — apartness is the antithesis
of equality — now with the refutation carrying *witness data* (a `Type`).
-/

universe u

namespace Antithesis
open scoped Antithesis

/-! ## Surface syntax -/

section Surface
variable (P Q R : AProp) (p q : Prop)

example : ⟬ P ⊗ Q ⟭ = P.tensor Q := rfl
example : ⟬ P ⊓ Q ⊸ R ⟭ = (P.with' Q).limp R := rfl
example : ⟬ ~ P ⟭ = P.perp := rfl
example : ⟬ ⟪p⟫ ⟭ = AProp.liftProp p := rfl

example : ⟬ P ⊗ Q ⟭ ⊢ ⟬ Q ⊗ P ⟭ := by antithesis
example : ⟬ ⟪p⟫ ⊓ ⟪q⟫ ⟭ ⊢ ⟬ ⟪p⟫ ⟭ := by antithesis

end Surface

/-! ## Apartness as the antithesis of equality -/

/-- An affine equivalence relation on `α`. -/
structure AEquiv (α : Type u) where
  /-- The affine relation. -/
  rel : α → α → AProp.{u}
  refl : ∀ x, Holds (rel x x)
  symm : ∀ x y, rel x y ⊢ rel y x
  trans : ∀ x y z, rel x y ⊗ rel y z ⊢ rel x z

namespace AEquiv
variable {α : Type u} (E : AEquiv α)

/-- The induced **apartness**: the refutation side `(x ~ y)⁻`, which may carry a
witness (it is a `Type`). -/
def apart (x y : α) : Type u := (E.rel x y).neg

/-- Apartness is irreflexive — the antithesis of reflexivity. -/
def apart_irrefl (x : α) : E.apart x x → Empty := (E.rel x x).excl (E.refl x)

/-- Apartness is symmetric — the antithesis of symmetry. -/
def apart_symm {x y : α} : E.apart x y → E.apart y x := (E.symm y x).2

/-- Substitution / weak cotransitivity — the antithesis of transitivity. -/
def apart_subst {x y z : α} (h : E.apart x z) :
    (Holds (E.rel x y) → E.apart y z) × (Holds (E.rel y z) → E.apart x y) :=
  (E.trans x y z).2 h

end AEquiv

/-- A witnessed apartness structure (the refutation carries data, e.g. a
separating modulus). -/
structure WApart (α : Type u) where
  /-- Evidence that `x` and `y` are apart. -/
  apart : α → α → AProp.{u}
  /-- The affirmation of `apart x y` *is* the witness type. -/
  refl_excl : ∀ x, (apart x x).pos → Empty

/-- From a witnessed apartness, the diagonal is uninhabited (constructively). -/
example {α : Type u} (A : WApart α) (x : α) : (A.apart x x).pos → Empty := A.refl_excl x

end Antithesis
