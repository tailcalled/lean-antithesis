import LeanAntithesis.Logic.Entail

/-!
# Lifting evidence into the antithesis interpretation

`lift A` turns a `Type` of evidence `A` into the affine proposition "`A` is
inhabited", with affirmation the truncation `Trunc' A` and refutation
`Trunc' A → Empty`.  Truncating makes the components propositions (subsingletons)
for *any* `A`, so `lift` is total; the witness in `A` is still recoverable into
subsingletons via unique choice.

`liftProp p` lifts an ordinary Lean `Prop`.
-/

universe u

namespace Antithesis
namespace AProp

/-- Lift a type of evidence to the affine proposition "`A` is inhabited". -/
def lift (A : Type u) : AProp.{u} := ⟨Trunc' A, Trunc' A → Empty, fun t f => f t⟩

@[simp] theorem lift_pos (A : Type u) : (lift A).pos = Trunc' A := rfl
@[simp] theorem lift_neg (A : Type u) : (lift A).neg = (Trunc' A → Empty) := rfl

/-- Lift an ordinary Lean proposition. -/
def liftProp (p : Prop) : AProp.{0} := lift (PLift p)

end AProp
end Antithesis
