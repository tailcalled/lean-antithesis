import LeanAntithesis.Math.Subsetoid
import LeanAntithesis.Math.Quotient
import LeanAntithesis.Math.Deriving

/-! Exercises subsetoids (carrier, inclusion, respectfulness) and quotients (the
collapsing congruence, projection, and universal property). -/

namespace Antithesis
open scoped Antithesis

inductive Two where
  | a | b
  deriving AEquiv

abbrev X : ASetoid := .of Two

/-! ## Subsetoids -/

-- the subsetoid carved out by `S` is itself a setoid
example : ASetoid := .of (Subsetoid X CSet.univ)
-- with the inclusion morphism into `X`
example : ASetoid.Hom (.of (Subsetoid X CSet.univ)) X := Subsetoid.incl
-- a member (the membership witness of `univ` is trivial)
example : Subsetoid X CSet.univ := ⟨Two.a, PUnit.unit⟩
-- `univ` respects equality
example : Subsetoid.Respects (X := X) CSet.univ :=
  fun _ _ => curry (cut tensor_comm tensor_weaken)

/-! ## Quotients -/

-- the total congruence collapses `X` to a point
def collapse : Congruence X where
  eqv := { rel := fun _ _ => AProp.top
           refl := fun _ => Entails.refl _
           symm := fun _ _ => Entails.refl _
           trans := fun _ _ _ => tensor_weaken }
  refines := fun _ _ => entails_top

example : ASetoid := collapse.quotient
example : ASetoid.Hom X collapse.quotient := collapse.proj
-- in the collapse, the two points become equal
example : Valid (collapse.quotient.eq Two.a Two.b) := Valid.of_holds PUnit.unit

-- universal property: a map constant up to `~` factors through the quotient
def constHom : ASetoid.Hom X X :=
  ⟨fun _ => Two.a, fun _ _ => Entails.of_holds (AEquiv.refl Two.a).holds⟩
example : ASetoid.Hom collapse.quotient X :=
  collapse.lift constHom fun _ _ => Entails.of_holds (AEquiv.refl Two.a).holds

/-! ## `Hom.ext` makes the category laws provable -/

open ASetoid in
example {W X Y Z : ASetoid} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext rfl

open ASetoid in
example {X Y : ASetoid} (f : Hom X Y) : f.comp (Hom.id X) = f := Hom.ext rfl

open ASetoid in
example {X Y : ASetoid} (f : Hom X Y) : (Hom.id Y).comp f = f := Hom.ext rfl

end Antithesis
