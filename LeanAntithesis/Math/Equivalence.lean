import LeanAntithesis.Math.ComplementedSet

/-!
# Affine equivalence relations, apartness, and setoids

An **affine equivalence relation** `AEquiv α` is an `AProp`-valued relation whose
affirmation is reflexive/symmetric/transitive.  Its refutation side is an
**apartness** `x # y := (x ~ y)ᗮ`, and the apartness axioms are *exactly* the
equivalence axioms dualized by `perp_mono` (Shulman: apartness is the antithesis
of equality).

A **setoid** `ASetoid` bundles a type with such a relation — a "set" in the
constructive (Bishop) sense.  Its morphisms are functions respecting `~`; they
automatically *reflect* `#`.
-/

universe u

namespace Antithesis
open scoped Antithesis

/-! ## The relation (a typeclass — derivable per type, like `DecidableEq`) -/

/-- A type `α` carries an affine equivalence relation. -/
class AEquiv (α : Type u) where
  /-- The relation; `(rel x y)⁺` affirms `x ~ y`, `(rel x y)⁻` is `x # y`. -/
  rel : α → α → AProp.{u}
  /-- Reflexivity. -/
  refl : ∀ x, Valid (rel x x)
  /-- Symmetry. -/
  symm : ∀ x y, rel x y ⊢ rel y x
  /-- Transitivity (multiplicative — composes via `cut`). -/
  trans : ∀ x y z, rel x y ⊗ rel y z ⊢ rel x z

namespace AEquiv
variable {α : Type u} [AEquiv α]

/-- The induced **apartness** `x # y`, the antithesis of `x ~ y`. -/
def apart (x y : α) : AProp.{u} := (rel x y)ᗮ

/-- Apartness is **irreflexive** — reflexivity dualized (`x # x ⊢ ⊥`). -/
def apart_irrefl (x : α) : apart x x ⊢ AProp.bot := perp_mono (refl x)

/-- Apartness is **symmetric** — symmetry dualized. -/
def apart_symm (x y : α) : apart x y ⊢ apart y x := perp_mono (symm y x)

/-- Apartness is **cotransitive** (the multiplicative `⅋` form) — transitivity
dualized: `x # z ⊢ (x # y) ⅋ (y # z)`. -/
def apart_cotrans (x y z : α) : apart x z ⊢ apart x y ⅋ apart y z :=
  perp_mono (trans x y z)

/-- The "singleton" complemented subset `{a}`: `x ∈ {a}` iff `a ~ x`. -/
def singleton (a : α) : CSet.{u} α := fun x => rel a x

/-- Its complement is exactly "apart from `a`". -/
theorem compl_singleton (a : α) : (singleton a)ᶜ = fun x => apart a x := rfl

end AEquiv

/-! ## Setoids: types equipped with an affine equivalence relation -/

/-- A type bundled with an affine equivalence relation — a "set" in the
constructive sense (equality `~`, apartness `#`).  Recover it from the class via
`ASetoid.of α`. -/
structure ASetoid : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  /-- The affine equivalence relation. -/
  eqv : AEquiv carrier

namespace ASetoid

instance : CoeSort ASetoid.{u} (Type u) := ⟨carrier⟩

/-- Bundle a type with its `AEquiv` instance. -/
def of (α : Type u) [e : AEquiv α] : ASetoid.{u} := ⟨α, e⟩

variable (X : ASetoid.{u})

/-- Equality on `X`. -/
def eq (x y : X) : AProp.{u} := X.eqv.rel x y
/-- Apartness on `X`. -/
def apart (x y : X) : AProp.{u} := X.eqv.apart x y

/-- A morphism of setoids: a function respecting `~`. -/
structure Hom (X Y : ASetoid.{u}) where
  /-- The underlying function. -/
  toFun : X → Y
  /-- It respects the equivalence relation. -/
  resp : ∀ x x', X.eq x x' ⊢ Y.eq (toFun x) (toFun x')

namespace Hom
variable {X Y Z : ASetoid.{u}}

/-- A morphism automatically **reflects** apartness. -/
def reflect_apart (f : Hom X Y) (x x' : X) :
    Y.apart (f.toFun x) (f.toFun x') ⊢ X.apart x x' :=
  perp_mono (f.resp x x')

/-- The identity morphism. -/
def id (X : ASetoid.{u}) : Hom X X := ⟨_root_.id, fun _ _ => Entails.refl _⟩

/-- Composition of morphisms. -/
def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z :=
  ⟨g.toFun ∘ f.toFun, fun x x' => cut (f.resp x x') (g.resp (f.toFun x) (f.toFun x'))⟩

end Hom
end ASetoid

end Antithesis
