/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Connectives

/-!
# Validity and entailment

An affine proposition `P` **holds** when its affirmation `P⁺` is provable.
Affine **entailment** `P ⊢ Q` is a Chu morphism: a proof that affirmation
transports forwards and refutation transports backwards,
`(P⁺ → Q⁺) ∧ (Q⁻ → P⁻)`.  This is definitionally the validity of `P ⊸ Q`.
-/

namespace Antithesis

/-- `P` holds / is affirmed: its positive part `P⁺` is provable. -/
def Holds (P : AProp) : Prop := P.pos

/-- `P` is refuted: its negative part `P⁻` is provable. -/
def Refuted (P : AProp) : Prop := P.neg

/-- Affine entailment `P ⊢ Q`, a Chu morphism `(P⁺ → Q⁺) ∧ (Q⁻ → P⁻)`. -/
def Entails (P Q : AProp) : Prop := (P.pos → Q.pos) ∧ (Q.neg → P.neg)

@[inherit_doc] scoped infix:50 " ⊢ " => Entails

@[simp] theorem holds_def (P : AProp) : Holds P ↔ P.pos := Iff.rfl
@[simp] theorem refuted_def (P : AProp) : Refuted P ↔ P.neg := Iff.rfl
@[simp] theorem entails_def (P Q : AProp) :
    Entails P Q ↔ (P.pos → Q.pos) ∧ (Q.neg → P.neg) := Iff.rfl

/-- Entailment is exactly the validity of linear implication. -/
theorem entails_iff_holds_limp (P Q : AProp) : Entails P Q ↔ Holds (P.limp Q) := Iff.rfl

/-! ## Entailment is a preorder -/

@[refl] theorem Entails.refl (P : AProp) : P ⊢ P := ⟨id, id⟩

theorem Entails.trans {P Q R : AProp} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  ⟨fun hp => h₂.1 (h₁.1 hp), fun hr => h₁.2 (h₂.2 hr)⟩

instance : Trans Entails Entails Entails where
  trans := Entails.trans

/-! ## Sanity checks: hand proofs validating the connective definitions

(Replaced by the `antithesis` tactic later — these are here to confirm the
math is right.) -/

section Sanity
variable (P Q : AProp)

/-- Affine weakening for `⊗` (needs exclusivity of `P`). -/
example : P.tensor Q ⊢ P :=
  ⟨fun ⟨hp, _⟩ => hp,
   fun hpn => ⟨fun hpp => absurd hpn (fun h => P.excl hpp h), fun _ => hpn⟩⟩

/-- `⊕`-introduction. -/
example : P ⊢ P.plus Q := ⟨fun hp => Or.inl hp, fun ⟨hpn, _⟩ => hpn⟩

/-- De Morgan: `(P ⊗ Q)ᗮ = Pᗮ ⅋ Qᗮ`, definitionally. -/
example : (P.tensor Q).perp = (P.perp.par Q.perp) := rfl

/-- De Morgan: `(P ⊓ Q)ᗮ = Pᗮ ⊔ Qᗮ`, definitionally. -/
example : (P.with' Q).perp = (P.perp.plus Q.perp) := rfl

end Sanity

end Antithesis
