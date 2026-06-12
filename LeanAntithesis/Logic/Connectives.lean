/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Logic.Core

/-!
# Affine connectives (Type-valued)

Each connective gives `pos`/`neg` evidence `Type`s and a proof they are jointly
uninhabited.  The multiplicative connectives use `×`/`→`; the **disjunctive and
existential** positions are propositionally truncated with `Trunc'` (so they are
mere propositions, matching the logic, while remaining computable).

Connectives are tagged `@[aesop norm unfold]` so the `antithesis` solver sees
through them; `@[simp]` projection lemmas are provided for manual use.

Notation is `scoped` in `Antithesis`.
-/

universe u v

namespace Antithesis
namespace AProp

/-! ## Units -/

/-- The unit `1 = ⊤ = (⊤, ⊥)`. -/
@[aesop norm unfold] def top : AProp.{u} := ⟨PUnit, PEmpty, fun _ e => e.elim⟩
/-- The unit `0 = ⊥ = (⊥, ⊤)`. -/
@[aesop norm unfold] def bot : AProp.{u} := ⟨PEmpty, PUnit, fun e _ => e.elim⟩

/-- Multiplicative unit `1`, equal to `⊤`. -/
abbrev one : AProp.{u} := top
/-- Additive unit `0`, equal to `⊥`. -/
abbrev zero : AProp.{u} := bot

@[simp] theorem top_pos : (top.{u}).pos = PUnit := rfl
@[simp] theorem top_neg : (top.{u}).neg = PEmpty := rfl
@[simp] theorem bot_pos : (bot.{u}).pos = PEmpty := rfl
@[simp] theorem bot_neg : (bot.{u}).neg = PUnit := rfl

/-! ## Linear negation -/

/-- Linear negation `Pᗮ = (P⁻, P⁺)`. -/
@[aesop norm unfold] def perp (P : AProp.{u}) : AProp.{u} := ⟨P.neg, P.pos, fun a b => P.excl b a⟩

@[simp] theorem perp_pos (P : AProp.{u}) : P.perp.pos = P.neg := rfl
@[simp] theorem perp_neg (P : AProp.{u}) : P.perp.neg = P.pos := rfl
@[simp] theorem perp_perp (P : AProp.{u}) : P.perp.perp = P := rfl

/-! ## Multiplicative connectives -/

/-- Multiplicative conjunction `P ⊗ Q`. -/
@[aesop norm unfold] def tensor (P Q : AProp.{u}) : AProp.{u} :=
  ⟨P.pos × Q.pos, (P.pos → Q.neg) × (Q.pos → P.neg),
    fun ⟨hp, hq⟩ ⟨f, _⟩ => Q.excl hq (f hp)⟩

/-- Multiplicative disjunction `P ⅋ Q`. -/
@[aesop norm unfold] def par (P Q : AProp.{u}) : AProp.{u} :=
  ⟨(P.neg → Q.pos) × (Q.neg → P.pos), P.neg × Q.neg,
    fun ⟨f, _⟩ ⟨hpn, hqn⟩ => Q.excl (f hpn) hqn⟩

/-- Linear implication `P ⊸ Q`. -/
@[aesop norm unfold] def limp (P Q : AProp.{u}) : AProp.{u} :=
  ⟨(P.pos → Q.pos) × (Q.neg → P.neg), P.pos × Q.neg,
    fun ⟨f, _⟩ ⟨hp, hqn⟩ => Q.excl (f hp) hqn⟩

@[simp] theorem tensor_pos (P Q : AProp.{u}) : (P.tensor Q).pos = (P.pos × Q.pos) := rfl
@[simp] theorem tensor_neg (P Q : AProp.{u}) :
    (P.tensor Q).neg = ((P.pos → Q.neg) × (Q.pos → P.neg)) := rfl
@[simp] theorem par_pos (P Q : AProp.{u}) :
    (P.par Q).pos = ((P.neg → Q.pos) × (Q.neg → P.pos)) := rfl
@[simp] theorem par_neg (P Q : AProp.{u}) : (P.par Q).neg = (P.neg × Q.neg) := rfl
@[simp] theorem limp_pos (P Q : AProp.{u}) :
    (P.limp Q).pos = ((P.pos → Q.pos) × (Q.neg → P.neg)) := rfl
@[simp] theorem limp_neg (P Q : AProp.{u}) : (P.limp Q).neg = (P.pos × Q.neg) := rfl

/-! ## Additive connectives (disjunctive position truncated) -/

/-- Additive conjunction `P ⊓ Q` ("with"); refutation is a truncated sum. -/
@[aesop norm unfold] def with' (P Q : AProp.{u}) : AProp.{u} :=
  ⟨P.pos × Q.pos, Trunc' (P.neg ⊕ Q.neg),
    fun ⟨hp, hq⟩ t => Trunc'.toEmpty (Sum.elim (P.excl hp) (Q.excl hq)) t⟩

/-- Additive disjunction `P ⊔ Q` ("plus"); affirmation is a truncated sum. -/
@[aesop norm unfold] def plus (P Q : AProp.{u}) : AProp.{u} :=
  ⟨Trunc' (P.pos ⊕ Q.pos), P.neg × Q.neg,
    fun t ⟨hpn, hqn⟩ => Trunc'.toEmpty (Sum.elim (P.excl · hpn) (Q.excl · hqn)) t⟩

@[simp] theorem with_pos (P Q : AProp.{u}) : (P.with' Q).pos = (P.pos × Q.pos) := rfl
@[simp] theorem with_neg (P Q : AProp.{u}) : (P.with' Q).neg = Trunc' (P.neg ⊕ Q.neg) := rfl
@[simp] theorem plus_pos (P Q : AProp.{u}) : (P.plus Q).pos = Trunc' (P.pos ⊕ Q.pos) := rfl
@[simp] theorem plus_neg (P Q : AProp.{u}) : (P.plus Q).neg = (P.neg × Q.neg) := rfl

/-! ## Exponentials -/

/-- Exponential `!P`. -/
@[aesop norm unfold] def bang (P : AProp.{u}) : AProp.{u} :=
  ⟨P.pos, P.pos → P.neg, fun hp f => P.excl hp (f hp)⟩
/-- Exponential `?P`. -/
@[aesop norm unfold] def quest (P : AProp.{u}) : AProp.{u} :=
  ⟨P.neg → P.pos, P.neg, fun f hn => P.excl (f hn) hn⟩

@[simp] theorem bang_pos (P : AProp.{u}) : P.bang.pos = P.pos := rfl
@[simp] theorem bang_neg (P : AProp.{u}) : P.bang.neg = (P.pos → P.neg) := rfl
@[simp] theorem quest_pos (P : AProp.{u}) : P.quest.pos = (P.neg → P.pos) := rfl
@[simp] theorem quest_neg (P : AProp.{u}) : P.quest.neg = P.neg := rfl

/-! ## Quantifiers (existential position truncated) -/

/-- Linear universal `⨅ x, P x`; refutation is a truncated sigma. -/
@[aesop norm unfold] def all {α : Type v} (P : α → AProp.{u}) : AProp.{max u v} :=
  ⟨(x : α) → (P x).pos, Trunc' ((x : α) × (P x).neg),
    fun f t => Trunc'.toEmpty (fun ⟨x, hx⟩ => (P x).excl (f x) hx) t⟩

/-- Linear existential `⨆ x, P x`; affirmation is a truncated sigma. -/
@[aesop norm unfold] def ex {α : Type v} (P : α → AProp.{u}) : AProp.{max u v} :=
  ⟨Trunc' ((x : α) × (P x).pos), (x : α) → (P x).neg,
    fun t f => Trunc'.toEmpty (fun ⟨x, hx⟩ => (P x).excl hx (f x)) t⟩

@[simp] theorem all_pos {α : Type v} (P : α → AProp.{u}) :
    (all P).pos = ((x : α) → (P x).pos) := rfl
@[simp] theorem all_neg {α : Type v} (P : α → AProp.{u}) :
    (all P).neg = Trunc' ((x : α) × (P x).neg) := rfl
@[simp] theorem ex_pos {α : Type v} (P : α → AProp.{u}) :
    (ex P).pos = Trunc' ((x : α) × (P x).pos) := rfl
@[simp] theorem ex_neg {α : Type v} (P : α → AProp.{u}) : (ex P).neg = ((x : α) → (P x).neg) := rfl

end AProp

/-! ## Notation (scoped) -/

@[inherit_doc] scoped postfix:max "ᗮ" => AProp.perp
@[inherit_doc] scoped infixr:72 " ⊗ " => AProp.tensor
@[inherit_doc] scoped infixr:71 " ⅋ " => AProp.par
@[inherit_doc] scoped infixr:70 " ⊓ " => AProp.with'
@[inherit_doc] scoped infixr:69 " ⊔ " => AProp.plus
@[inherit_doc] scoped infixr:60 " ⊸ " => AProp.limp
@[inherit_doc] scoped prefix:max "！" => AProp.bang
@[inherit_doc] scoped prefix:max "？" => AProp.quest

end Antithesis
