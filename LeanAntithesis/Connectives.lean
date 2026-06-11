/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Core

/-!
# Affine connectives

Each affine connective is interpreted by giving its affirmation `pos`, its
refutation `neg`, and a proof that they remain mutually exclusive.  The
exclusivity proofs are discharged here once and for all, so downstream code
never has to think about them.

For every connective we also record `@[simp]` lemmas computing `.pos` and
`.neg`.  These reduce any goal about affine propositions to ordinary
intuitionistic logic, which is what the solver tactic relies on.

Notation is `scoped` in namespace `Antithesis`: write `open scoped Antithesis`
to bring it into scope, avoiding clashes with Mathlib's `⊓`, `⊔`, `⊗`, etc.
-/

namespace Antithesis
namespace AProp

/-! ## Units

In affine logic the multiplicative unit `1` and additive truth `⊤` coincide,
as do the multiplicative `⊥` and additive `0`.  So there are only two. -/

/-- The unit `1 = ⊤ = (⊤, ⊥)`. -/
def top : AProp := ⟨True, False, fun _ h => h⟩

/-- The unit `0 = ⊥ = (⊥, ⊤)`. -/
def bot : AProp := ⟨False, True, fun h _ => h⟩

/-- Multiplicative unit `1`, equal to `⊤`. -/
abbrev one : AProp := top
/-- Additive unit `0`, equal to `⊥`. -/
abbrev zero : AProp := bot

@[simp] theorem top_pos : top.pos = True := rfl
@[simp] theorem top_neg : top.neg = False := rfl
@[simp] theorem bot_pos : bot.pos = False := rfl
@[simp] theorem bot_neg : bot.neg = True := rfl

/-! ## Linear negation -/

/-- Linear negation `Pᗮ = (P⁻, P⁺)`: swap affirmation and refutation. -/
def perp (P : AProp) : AProp := ⟨P.neg, P.pos, fun hn hp => P.excl hp hn⟩

@[simp] theorem perp_pos (P : AProp) : P.perp.pos = P.neg := rfl
@[simp] theorem perp_neg (P : AProp) : P.perp.neg = P.pos := rfl

/-- Negation is involutive (definitionally). -/
@[simp] theorem perp_perp (P : AProp) : P.perp.perp = P := rfl

/-! ## Additive connectives -/

/-- Additive conjunction `P ⊓ Q = (P⁺ ∧ Q⁺, P⁻ ∨ Q⁻)` ("with"). -/
def with' (P Q : AProp) : AProp :=
  ⟨P.pos ∧ Q.pos, P.neg ∨ Q.neg, fun ⟨hp, hq⟩ h => h.elim (P.excl hp) (Q.excl hq)⟩

/-- Additive disjunction `P ⊔ Q = (P⁺ ∨ Q⁺, P⁻ ∧ Q⁻)` ("plus"). -/
def plus (P Q : AProp) : AProp :=
  ⟨P.pos ∨ Q.pos, P.neg ∧ Q.neg,
    fun h ⟨hp, hq⟩ => h.elim (fun x => P.excl x hp) (fun x => Q.excl x hq)⟩

@[simp] theorem with_pos (P Q : AProp) : (P.with' Q).pos = (P.pos ∧ Q.pos) := rfl
@[simp] theorem with_neg (P Q : AProp) : (P.with' Q).neg = (P.neg ∨ Q.neg) := rfl
@[simp] theorem plus_pos (P Q : AProp) : (P.plus Q).pos = (P.pos ∨ Q.pos) := rfl
@[simp] theorem plus_neg (P Q : AProp) : (P.plus Q).neg = (P.neg ∧ Q.neg) := rfl

/-! ## Multiplicative connectives -/

/-- Multiplicative conjunction `P ⊗ Q = (P⁺ ∧ Q⁺, (P⁺ ⇒ Q⁻) ∧ (Q⁺ ⇒ P⁻))`
("tensor"). -/
def tensor (P Q : AProp) : AProp :=
  ⟨P.pos ∧ Q.pos, (P.pos → Q.neg) ∧ (Q.pos → P.neg),
    fun ⟨hp, hq⟩ ⟨f, _⟩ => Q.excl hq (f hp)⟩

/-- Multiplicative disjunction `P ⅋ Q = ((P⁻ ⇒ Q⁺) ∧ (Q⁻ ⇒ P⁺), P⁻ ∧ Q⁻)`
("par"). -/
def par (P Q : AProp) : AProp :=
  ⟨(P.neg → Q.pos) ∧ (Q.neg → P.pos), P.neg ∧ Q.neg,
    fun ⟨f, _⟩ ⟨hpn, hqn⟩ => Q.excl (f hpn) hqn⟩

/-- Linear implication `P ⊸ Q = ((P⁺ ⇒ Q⁺) ∧ (Q⁻ ⇒ P⁻), P⁺ ∧ Q⁻)`. -/
def limp (P Q : AProp) : AProp :=
  ⟨(P.pos → Q.pos) ∧ (Q.neg → P.neg), P.pos ∧ Q.neg,
    fun ⟨f, _⟩ ⟨hpp, hqn⟩ => Q.excl (f hpp) hqn⟩

@[simp] theorem tensor_pos (P Q : AProp) : (P.tensor Q).pos = (P.pos ∧ Q.pos) := rfl
@[simp] theorem tensor_neg (P Q : AProp) :
    (P.tensor Q).neg = ((P.pos → Q.neg) ∧ (Q.pos → P.neg)) := rfl
@[simp] theorem par_pos (P Q : AProp) :
    (P.par Q).pos = ((P.neg → Q.pos) ∧ (Q.neg → P.pos)) := rfl
@[simp] theorem par_neg (P Q : AProp) : (P.par Q).neg = (P.neg ∧ Q.neg) := rfl
@[simp] theorem limp_pos (P Q : AProp) :
    (P.limp Q).pos = ((P.pos → Q.pos) ∧ (Q.neg → P.neg)) := rfl
@[simp] theorem limp_neg (P Q : AProp) : (P.limp Q).neg = (P.pos ∧ Q.neg) := rfl

/-! ## Exponentials -/

/-- Exponential conjunction `!P = (P⁺, P⁺ ⇒ P⁻)` ("of course"). -/
def bang (P : AProp) : AProp := ⟨P.pos, P.pos → P.neg, fun hp f => P.excl hp (f hp)⟩

/-- Exponential disjunction `?P = (P⁻ ⇒ P⁺, P⁻)` ("why not"). -/
def quest (P : AProp) : AProp := ⟨P.neg → P.pos, P.neg, fun f hn => P.excl (f hn) hn⟩

@[simp] theorem bang_pos (P : AProp) : P.bang.pos = P.pos := rfl
@[simp] theorem bang_neg (P : AProp) : P.bang.neg = (P.pos → P.neg) := rfl
@[simp] theorem quest_pos (P : AProp) : P.quest.pos = (P.neg → P.pos) := rfl
@[simp] theorem quest_neg (P : AProp) : P.quest.neg = P.neg := rfl

/-! ## Quantifiers -/

/-- Linear universal `⨅ x, P x = (∀ x, (P x)⁺, ∃ x, (P x)⁻)`. -/
def all {α : Sort*} (P : α → AProp) : AProp :=
  ⟨∀ x, (P x).pos, ∃ x, (P x).neg, fun hall ⟨x, hx⟩ => (P x).excl (hall x) hx⟩

/-- Linear existential `⨆ x, P x = (∃ x, (P x)⁺, ∀ x, (P x)⁻)`. -/
def ex {α : Sort*} (P : α → AProp) : AProp :=
  ⟨∃ x, (P x).pos, ∀ x, (P x).neg, fun ⟨x, hx⟩ hall => (P x).excl hx (hall x)⟩

@[simp] theorem all_pos {α : Sort*} (P : α → AProp) : (all P).pos = (∀ x, (P x).pos) := rfl
@[simp] theorem all_neg {α : Sort*} (P : α → AProp) : (all P).neg = (∃ x, (P x).neg) := rfl
@[simp] theorem ex_pos {α : Sort*} (P : α → AProp) : (ex P).pos = (∃ x, (P x).pos) := rfl
@[simp] theorem ex_neg {α : Sort*} (P : α → AProp) : (ex P).neg = (∀ x, (P x).neg) := rfl

end AProp

/-! ## Notation

Scoped in `Antithesis`.  Use `open scoped Antithesis` to enable. -/

@[inherit_doc] scoped postfix:max "ᗮ" => AProp.perp
@[inherit_doc] scoped infixr:72 " ⊗ " => AProp.tensor
@[inherit_doc] scoped infixr:71 " ⅋ " => AProp.par
@[inherit_doc] scoped infixr:70 " ⊓ " => AProp.with'
@[inherit_doc] scoped infixr:69 " ⊔ " => AProp.plus
@[inherit_doc] scoped infixr:60 " ⊸ " => AProp.limp
@[inherit_doc] scoped prefix:max "！" => AProp.bang
@[inherit_doc] scoped prefix:max "？" => AProp.quest

end Antithesis
