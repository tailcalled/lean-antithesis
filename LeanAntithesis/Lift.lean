/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Entail

/-!
# Lifting ordinary propositions into the antithesis interpretation

The canonical embedding sends an intuitionistic proposition `p` to the affine
proposition `(p, ¬p)`: affirmation is `p`, refutation is its negation.  This is
the obvious atom whose refutation carries no extra constructive content.

Mathematical atoms often have a *stronger* refutation than `¬p` (e.g. equality
refuted by apartness `#`, rather than by `≠`).  Those are built directly with
the `AProp` constructor `⟨pos, neg, h⟩`, supplying the proof that the chosen
refutation is incompatible with the affirmation. -/

namespace Antithesis
namespace AProp

/-- Canonical lift of an ordinary proposition: `lift p = (p, ¬p)`. -/
def lift (p : Prop) : AProp := ⟨p, ¬p, fun hp hnp => hnp hp⟩

@[simp] theorem lift_pos (p : Prop) : (lift p).pos = p := rfl
@[simp] theorem lift_neg (p : Prop) : (lift p).neg = ¬p := rfl

@[simp] theorem holds_lift (p : Prop) : Holds (lift p) ↔ p := Iff.rfl
@[simp] theorem refuted_lift (p : Prop) : Refuted (lift p) ↔ ¬p := Iff.rfl

/-- `lift` of `True`/`False` are the affine units. -/
@[simp] theorem lift_true : lift True = top := by ext <;> simp [top]
@[simp] theorem lift_false : lift False = bot := by ext <;> simp [bot]

end AProp
end Antithesis
