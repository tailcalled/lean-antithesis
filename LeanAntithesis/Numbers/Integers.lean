import LeanAntithesis.Sets.Discrete
import Mathlib.Data.Int.Notation

/-!
# The integers as an affine set

`ℤ` has decidable equality, so its antithesis structure is the discrete one:
`m ~ n` is `m = n` and the apartness `m # n` is the (decidable) `m ≠ n`.  Being
discrete, every integer operation is automatically a setoid morphism.
-/

namespace Antithesis
open scoped Antithesis

/-- The integers as an affine set: `~` is `=`, `#` is decidable `≠`. -/
instance : AEquiv ℤ := discrete ℤ

example : Valid (AEquiv.rel (2 : ℤ) 2) := AEquiv.refl _
example : Valid (AEquiv.apart (1 : ℤ) 2) := discrete.apart_of_ne (by decide)
example : Valid (AEquiv.apart (-3 : ℤ) 3) := discrete.apart_of_ne (by decide)

/-- `ℤ` is a first-class affine set. -/
example : ASetoid := .of ℤ

/-- Negation is a setoid morphism (as is every integer operation). -/
def negHom : ASetoid.Hom (.of ℤ) (.of ℤ) := ⟨Int.neg, discrete.resp Int.neg⟩

/-- Translation by a fixed integer is a morphism. -/
def addHom (k : ℤ) : ASetoid.Hom (.of ℤ) (.of ℤ) :=
  ⟨fun n : ℤ => n + k, discrete.resp fun n : ℤ => n + k⟩

end Antithesis
