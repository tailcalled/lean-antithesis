import LeanAntithesis.Math.SetoidAlgebra

/-! Exercises the setoid algebra: derived product/sum setoids close under `aequiv`,
and the hand-built function setoid supports reflexivity and "differ somewhere"
apartness. -/

namespace Antithesis
open scoped Antithesis

inductive E where
  | a | b
  deriving AEquiv

/-! ## Products -/

example : Valid (AEquiv.rel ((E.a, E.b)) ((E.a, E.b))) := by aequiv
-- apart in the first coordinate — abstract second coordinate is irrelevant
example (x y : E) : Valid (AEquiv.apart ((E.a, x)) ((E.b, y))) := by aequiv
-- apart in the second coordinate
example : Valid (AEquiv.apart ((E.a, E.a)) ((E.a, E.b))) := by aequiv

/-! ## Sums -/

example : Valid (AEquiv.rel (Sum.inl E.a : E ⊕ E) (Sum.inl E.a)) := by aequiv
-- different injections are apart
example (x y : E) : Valid (AEquiv.apart (Sum.inl x : E ⊕ E) (Sum.inr y)) := by aequiv
-- same injection, apart contents
example : Valid (AEquiv.apart (Sum.inl E.a : E ⊕ E) (Sum.inl E.b)) := by aequiv

/-! ## The function setoid -/

-- reflexivity comes from the instance
example (f : Bool → E) : Valid (AEquiv.rel f f) := AEquiv.refl _

-- functions apart somewhere: supply the point and the apartness there.  (`aequiv`
-- can't guess the existential witness, so this stays explicit by nature.)
example : Valid (AEquiv.apart (fun _ : Bool => E.a) (fun _ => E.b)) :=
  Valid.of_holds (Trunc'.mk ⟨true, Trunc'.mk E.Apart.a_b⟩)

-- the function setoid is a first-class object
example : ASetoid := ASetoid.of (Bool → E)

end Antithesis
