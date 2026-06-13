import LeanAntithesis.Logic.Connectives

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

/-- `A` is **valid** (a theorem): the unit entails it, `𝟙 ⊢ A`.  Being a sequent,
this composes with the calculus via `cut` — unlike the bare projection `Holds`. -/
abbrev Valid (A : AProp.{u}) : Type u := AProp.top ⊢ A

/-- Validity gives affirmation. -/
def Valid.holds {A : AProp.{u}} (h : Valid A) : Holds A := h.1 PUnit.unit

/-- Affirmation gives validity (the refutation side follows from `excl`). -/
def Valid.of_holds {A : AProp.{u}} (h : Holds A) : Valid A :=
  ⟨fun _ => h, fun hn => (A.excl h hn).elim⟩

namespace Entails

/-- Identity entailment. -/
def refl (P : AProp.{u}) : P ⊢ P := ⟨id, id⟩

/-- Composition / cut (composes the underlying realizers). -/
def trans {P : AProp.{u}} {Q : AProp.{v}} {R : AProp.{w}} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  ⟨fun hp => h₂.1 (h₁.1 hp), fun hr => h₁.2 (h₂.2 hr)⟩

/-- A valid conclusion holds in **any** context (affine weakening): an affirmation
of `A` entails `A` from any `Γ`.  Generalises `Valid.of_holds` (the `Γ = 𝟙` case)
so concrete facts can be discharged inside a larger sequent. -/
def of_holds {Γ : AProp.{v}} {A : AProp.{u}} (h : Holds A) : Γ ⊢ A :=
  ⟨fun _ => h, fun hn => (A.excl h hn).elim⟩

end Entails

/-- `calc` support for `⊢` (single universe). -/
instance : Trans (α := AProp.{u}) (β := AProp.{u}) (γ := AProp.{u}) Entails Entails Entails :=
  ⟨Entails.trans⟩

end Antithesis
