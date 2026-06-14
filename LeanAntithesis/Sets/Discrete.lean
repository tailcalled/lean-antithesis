import LeanAntithesis.Sets.Equivalence

/-!
# Discrete affine sets

The **discrete** setoid on a type: `x ~ y` is Lean equality and `x # y` is its
denial `x ≠ y`.  For a type with *decidable* equality (`ℕ`, `ℤ`, `Bool`, …) the
denial is a genuine, decidable apartness, so this is the correct antithesis
structure on such "discrete" sets.

Because equality is the finest relation, **every** function out of a discrete set
respects it — so functions between discrete sets are automatically setoid
morphisms.
-/

namespace Antithesis
open scoped Antithesis

/-- The discrete affine equivalence on a type: `~` is `=`, `#` is `≠`. -/
@[reducible] def discrete (α : Type) : AEquiv α where
  rel x y := AProp.ofTypes (PLift (x = y)) (PLift (x ≠ y)) fun p q => absurd p.down q.down
  refl _ := Valid.of_holds (Trunc'.mk ⟨rfl⟩)
  symm _ _ := AProp.ofTypes_mono (fun p => ⟨p.down.symm⟩) (fun q => ⟨fun h => q.down h.symm⟩)
  trans _ _ _ := AProp.ofTypes_tensor
    (fun p q => ⟨p.down.trans q.down⟩)
    (fun p r => ⟨fun h => r.down (p.down.trans h)⟩)
    (fun q r => ⟨fun h => r.down (h.trans q.down)⟩)

namespace discrete
variable {α β : Type}

/-- Equal elements are related. -/
def rel_of_eq {x y : α} (h : x = y) : Valid ((discrete α).rel x y) :=
  Valid.of_holds (Trunc'.mk ⟨h⟩)

/-- Unequal elements are apart. -/
def apart_of_ne {x y : α} (h : x ≠ y) : Valid ((discrete α).rel x y)ᗮ :=
  Valid.of_holds (Trunc'.mk ⟨h⟩)

/-- Every function respects discrete equality (`=` is the finest relation), so it
is a setoid morphism. -/
def resp (f : α → β) (x y : α) : (discrete α).rel x y ⊢ (discrete β).rel (f x) (f y) :=
  AProp.ofTypes_mono (fun p => ⟨congrArg f p.down⟩) (fun q => ⟨fun h => q.down (congrArg f h)⟩)

end discrete
end Antithesis
