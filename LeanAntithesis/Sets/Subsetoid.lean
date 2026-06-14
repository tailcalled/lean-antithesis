import LeanAntithesis.Sets.Equivalence

/-!
# Subsetoids

A **subsetoid** of a setoid `X` is carved out by a complemented subset
`S : CSet X`: its elements are points of `X` paired with a *membership witness*,
and it inherits `X`'s equality (membership witnesses are irrelevant up to `~`,
since `(S x).pos` is a subsingleton).  The inclusion into `X` is a setoid
morphism, and it automatically reflects apartness (it is "injective").

`S` **respects** `X`'s equality when equal points are members together; a
respectful subset transports membership along `~`.
-/

universe u

namespace Antithesis
open scoped Antithesis

/-- The subsetoid carved out by a complemented subset `S` of `X`: a point together
with a witness that it lies in `S`. -/
def Subsetoid (X : ASetoid.{u}) (S : CSet.{u} X.carrier) : Type u :=
  (x : X.carrier) × Holds (S x)

namespace Subsetoid
variable {X : ASetoid.{u}} {S : CSet.{u} X.carrier}

/-- Equality on the subsetoid is `X`'s equality on the underlying points. -/
instance : AEquiv (Subsetoid X S) where
  rel a b := X.eqv.rel a.1 b.1
  refl a := X.eqv.refl a.1
  symm a b := X.eqv.symm a.1 b.1
  trans a b c := X.eqv.trans a.1 b.1 c.1

/-- The inclusion `S ↪ X` as a setoid morphism. -/
def incl : ASetoid.Hom (.of (Subsetoid X S)) X :=
  ⟨fun a => a.1, fun _ _ => Entails.refl _⟩

/-- `S` **respects** `X`'s equality: equal points are members together (so
membership is a genuine property of the `~`-class). -/
def Respects (S : CSet.{u} X.carrier) : Type u := ∀ x y, X.eq x y ⊢ (S x ⊸ S y)

/-- A respectful subset transports membership along equality. -/
def Respects.mem (h : Respects S) {x y : X.carrier} (e : Valid (X.eq x y))
    (hx : Holds (S x)) : Holds (S y) := ((h x y).1 e.holds).1 hx

end Subsetoid
end Antithesis
