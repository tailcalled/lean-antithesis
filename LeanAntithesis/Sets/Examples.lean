import LeanAntithesis.Logic.Tactic
import LeanAntithesis.Logic.Calculus
import LeanAntithesis.Logic.Syntax

/-!
# Examples: the surface syntax

A showcase of the `⟬ ⟭` translation macro.  (The mathematics — complemented
subsets, apartness — lives in its own files.)
-/

namespace Antithesis
open scoped Antithesis

section Surface
variable (P Q R : AProp) (p q : Prop)

-- The brackets translate to the named connectives, definitionally.
example : ⟬ P ⊗ Q ⟭ = P.tensor Q := rfl
example : ⟬ P ⊓ Q ⊸ R ⟭ = (P.with' Q).limp R := rfl
example : ⟬ ~ P ⟭ = P.perp := rfl

-- A `Prop` atom is lifted; an `AProp` atom is embedded directly.
example : ⟬ ⟪p⟫ ⟭ = AProp.liftProp p := rfl

-- ...and the solver proves entailments stated in surface syntax.
example : ⟬ P ⊗ Q ⟭ ⊢ ⟬ Q ⊗ P ⟭ := by antithesis
example : ⟬ ⟪p⟫ ⊓ ⟪q⟫ ⟭ ⊢ ⟬ ⟪p⟫ ⟭ := by antithesis

end Surface

end Antithesis
