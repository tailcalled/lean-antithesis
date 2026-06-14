import LeanAntithesis.Math.Equivalence

/-!
# Quotient setoids

Dually to a subsetoid, a **quotient** of a setoid `X` is given by a *congruence*:
a coarser equivalence relation `R` (one for which `X`-equal points are already
`R`-related).  The quotient `X / R` keeps `X`'s carrier but uses the coarser
equality, the projection `X ↠ X / R` is a morphism, and it enjoys the universal
property: any morphism out of `X` that respects `R` factors through it.
-/

universe u

namespace Antithesis
open scoped Antithesis

/-- A **congruence** on `X`: a coarser equivalence relation.  `refines` says
`X`-equal points are `R`-congruent — exactly what makes the projection a
morphism. -/
structure Congruence (X : ASetoid.{u}) where
  /-- The coarser equivalence relation. -/
  eqv : AEquiv X.carrier
  /-- `X`-equality refines the congruence. -/
  refines : ∀ x y, X.eq x y ⊢ eqv.rel x y

namespace Congruence
variable {X : ASetoid.{u}} (R : Congruence X)

/-- The quotient setoid `X / R`: same carrier, coarser equality. -/
def quotient : ASetoid.{u} := ⟨X.carrier, R.eqv⟩

/-- The quotient projection `X ↠ X / R`. -/
def proj : ASetoid.Hom X R.quotient := ⟨id, R.refines⟩

/-- Universal property: a morphism `f : X ⟶ Y` that respects `R` (sends
`R`-congruent points to `~`-equal ones) factors through the quotient. -/
def lift {Y : ASetoid.{u}} (f : ASetoid.Hom X Y)
    (hf : ∀ x y, R.eqv.rel x y ⊢ Y.eq (f.toFun x) (f.toFun y)) :
    ASetoid.Hom R.quotient Y := ⟨f.toFun, hf⟩

/-- The factorization `(lift f) ∘ proj = f` (as morphisms, via `Hom.ext`). -/
theorem lift_proj {Y : ASetoid.{u}} (f : ASetoid.Hom X Y)
    (hf : ∀ x y, R.eqv.rel x y ⊢ Y.eq (f.toFun x) (f.toFun y)) :
    (R.lift f hf).comp R.proj = f := ASetoid.Hom.ext rfl

end Congruence
end Antithesis
