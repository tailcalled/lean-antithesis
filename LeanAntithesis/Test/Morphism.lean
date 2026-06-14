import LeanAntithesis.Sets.Morphism
import LeanAntithesis.Sets.SetoidAlgebra
import LeanAntithesis.Numbers.Integers

/-! `mor` derives `resp` for pointfully-written morphisms: one-shot on discrete
domains, by peeling named morphisms on non-discrete ones. -/

namespace Antithesis
open scoped Antithesis

-- discrete domain: `mor` closes pointful infix / polynomial in one shot
def poly : ASetoid.Hom (.of ℤ) (.of ℤ) := ⟨fun a : ℤ => a * a + 2 * a - 3, by mor⟩

-- CoeFun: morphisms apply like ordinary functions
example (a : ℤ) : ℤ := negHom (negHom a)

-- a morphism out of the (non-discrete) function setoid `Bool → ℤ`
def ev : ASetoid.Hom (.of (Bool → ℤ)) (.of ℤ) := ⟨fun f => f true, fun _ _ => all_elim true⟩

-- NON-discrete domain: `mor` peels the named morphisms `negHom` and `ev`
def negEval : ASetoid.Hom (.of (Bool → ℤ)) (.of ℤ) :=
  ⟨fun f => negHom (ev f), by mor⟩

-- BINARY op on a SHARED variable over a non-discrete domain: `mor` pairs the two
-- sub-proofs (cartesian `with_intro`, no contraction) then applies `+`'s congruence
def addEval (f g : ASetoid.Hom (.of (Bool → ℤ)) (.of ℤ)) :
    ASetoid.Hom (.of (Bool → ℤ)) (.of ℤ) :=
  ⟨fun h => f h + g h, by mor⟩

-- a polynomial combination of named morphisms, all pointful
def poly2 (f g : ASetoid.Hom (.of (Bool → ℤ)) (.of ℤ)) :
    ASetoid.Hom (.of (Bool → ℤ)) (.of ℤ) :=
  ⟨fun h => negHom (f h * g h) - ev h, by mor⟩

end Antithesis
