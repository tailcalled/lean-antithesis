/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Connectives

/-!
# Validity and entailment (as data)

`P` **holds** when its affirmation `P⁺` is inhabited.  An **entailment** `P ⊢ Q`
is now genuine *data* — a Chu morphism `(P⁺ → Q⁺) × (Q⁻ → P⁻)` — so inhabiting
it *is* the constructive content (a realizer), and it is computable.

Entailment is universe-heterogeneous, which is what lets quantifier rules relate
`⨅ x, P x : AProp.{max u v}` to `P a : AProp.{u}`.
-/

universe u v w

namespace Antithesis

/-- `P` holds: its affirmation `P⁺` is inhabited. -/
abbrev Holds (P : AProp.{u}) : Type u := P.pos

/-- `P` is refuted: its refutation `P⁻` is inhabited. -/
abbrev Refuted (P : AProp.{u}) : Type u := P.neg

/-- Affine entailment as data: affirmation forwards, refutation backwards. -/
@[aesop norm unfold]
def Entails (P : AProp.{u}) (Q : AProp.{v}) : Type (max u v) :=
  (P.pos → Q.pos) × (Q.neg → P.neg)

@[inherit_doc] scoped infix:50 " ⊢ " => Entails

/-- Entailment is, definitionally, the validity of linear implication. -/
theorem entails_eq_holds_limp (P Q : AProp.{u}) : (P ⊢ Q) = Holds (P.limp Q) := rfl

namespace Entails

/-- Identity entailment. -/
def refl (P : AProp.{u}) : P ⊢ P := ⟨id, id⟩

/-- Composition / cut (composes the underlying realizers). -/
def trans {P : AProp.{u}} {Q : AProp.{v}} {R : AProp.{w}} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  ⟨fun hp => h₂.1 (h₁.1 hp), fun hr => h₁.2 (h₂.2 hr)⟩

end Entails

/-- `calc` support for `⊢` (single universe). -/
instance : Trans (α := AProp.{u}) (β := AProp.{u}) (γ := AProp.{u}) Entails Entails Entails :=
  ⟨Entails.trans⟩

end Antithesis
