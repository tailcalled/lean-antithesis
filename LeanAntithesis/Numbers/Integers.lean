import LeanAntithesis.Sets.Morphism
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

/-! ## Congruence witnesses for the arithmetic operations

Being discrete, every operation respects `~`, so all the congruence instances are
populated by the `discrete.cong*` builders. -/

instance : NegCong ℤ := ⟨discrete.cong₁ fun a => -a⟩
instance : AddCong ℤ := ⟨discrete.cong₂ (· + ·)⟩
instance : SubCong ℤ := ⟨discrete.cong₂ (· - ·)⟩
instance : MulCong ℤ := ⟨discrete.cong₂ (· * ·)⟩

-- the witnesses are now available by instance resolution
example {a a' b b' : ℤ} :
    AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a + b) (a' + b') := AddCong.add_cong
example {a a' b b' : ℤ} :
    AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a * b) (a' * b') := MulCong.mul_cong
example {a a' : ℤ} : AEquiv.rel a a' ⊢ AEquiv.rel (-a) (-a') := NegCong.neg_cong

end Antithesis
