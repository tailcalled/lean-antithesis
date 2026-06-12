/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Logic.Tactic

/-!
# The affine sequent calculus, as composable entailment realizers

Each rule is a `def` producing the entailment *data* (a realizer).  Structural
rules are built by the `antithesis` solver; the additive **elimination** rules
(`⊓`-intro, `⊔`-elim, `⨅`-intro, `⨆`-elim) eliminate a truncated position into a
subsingleton component and so are built with `Trunc'.elimProp`.
-/

universe u v w

namespace Antithesis
open scoped Antithesis

variable {P P' Q Q' R : AProp.{u}}

/-! ## Cut and duality -/

/-- Cut / composition (universe-polymorphic, for relating different levels). -/
def cut {P : AProp.{u}} {Q : AProp.{v}} {R : AProp.{w}} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  Entails.trans h₁ h₂

/-- Contraposition: an entailment yields one between the duals. -/
def perp_mono (h : P ⊢ Q) : Qᗮ ⊢ Pᗮ := ⟨h.2, h.1⟩

/-- The reverse of `perp_mono` (used by the `ldualize` tactic). -/
def dualizeRev (h : Qᗮ ⊢ Pᗮ) : P ⊢ Q := ⟨h.2, h.1⟩

/-! ## Multiplicative -/

def tensor_mono (h₁ : P ⊢ P') (h₂ : Q ⊢ Q') : P ⊗ Q ⊢ P' ⊗ Q' := by antithesis
def tensor_comm : P ⊗ Q ⊢ Q ⊗ P := by antithesis
def tensor_assoc : (P ⊗ Q) ⊗ R ⊢ P ⊗ (Q ⊗ R) :=
  ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩,
   fun x => ⟨fun ⟨hp, hq⟩ => (x.1 hp).1 hq,
             fun hr => ⟨fun hp => (x.1 hp).2 hr, fun hq => x.2 ⟨hq, hr⟩⟩⟩⟩
def tensor_assoc' : P ⊗ (Q ⊗ R) ⊢ (P ⊗ Q) ⊗ R :=
  ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩,
   fun x => ⟨fun hp => ⟨fun hq => x.1 ⟨hp, hq⟩, fun hr => (x.2 hr).1 hp⟩,
             fun ⟨hq, hr⟩ => (x.2 hr).2 hq⟩⟩
def tensor_unit : P ⊗ AProp.top ⊢ P := by antithesis
def unit_tensor : P ⊢ P ⊗ AProp.top := by antithesis
/-- Affine weakening. -/
def tensor_weaken : P ⊗ Q ⊢ P := by antithesis
/-- Evaluation / linear modus ponens. -/
def eval : (P ⊸ Q) ⊗ P ⊢ Q := by antithesis
/-- The `⊗ ⊣ ⊸` adjunction. -/
def curry (h : P ⊗ Q ⊢ R) : P ⊢ Q ⊸ R :=
  ⟨fun hp => ⟨fun hq => h.1 ⟨hp, hq⟩, fun hrn => (h.2 hrn).1 hp⟩,
   fun ⟨hq, hrn⟩ => (h.2 hrn).2 hq⟩
def uncurry (h : P ⊢ Q ⊸ R) : P ⊗ Q ⊢ R :=
  ⟨fun ⟨hp, hq⟩ => (h.1 hp).1 hq,
   fun hrn => ⟨fun hp => (h.1 hp).2 hrn, fun hq => h.2 ⟨hq, hrn⟩⟩⟩
def limp_mono (h₁ : P' ⊢ P) (h₂ : Q ⊢ Q') : (P ⊸ Q) ⊢ (P' ⊸ Q') := by antithesis

/-! ## Additive -/

def with_fst : P ⊓ Q ⊢ P := by antithesis
def with_snd : P ⊓ Q ⊢ Q := by antithesis
/-- `⊓`-introduction (eliminates the truncated `⊔` in the refutation). -/
def with_intro (h₁ : R ⊢ P) (h₂ : R ⊢ Q) : R ⊢ P ⊓ Q :=
  ⟨fun hr => ⟨h₁.1 hr, h₂.1 hr⟩, Trunc'.elimProp (Sum.elim h₁.2 h₂.2)⟩

def plus_inl : P ⊢ P ⊔ Q := by antithesis
def plus_inr : Q ⊢ P ⊔ Q := by antithesis
/-- `⊔`-elimination (the fundamental rule for *using* a disjunction). -/
def plus_elim (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : P ⊔ Q ⊢ R :=
  ⟨Trunc'.elimProp (Sum.elim h₁.1 h₂.1), fun hr => ⟨h₁.2 hr, h₂.2 hr⟩⟩

/-- Dereliction `!P ⊢ P`. -/
def derelict : AProp.bang P ⊢ P := by antithesis

/-! ## Units and De Morgan -/

def bot_entails : AProp.bot ⊢ P := by antithesis
def entails_top : P ⊢ AProp.top := by antithesis

/-- Multiplicative non-contradiction: `P ⊗ Pᗮ ⊢ ⊥` (holds outright). -/
def tensor_perp_bot : P ⊗ Pᗮ ⊢ AProp.bot := by antithesis

/-- Additive non-contradiction *with the exponential*: `!(P ⊓ Pᗮ) ⊢ ⊥`.

The bare `P ⊓ Pᗮ ⊢ ⊥` is NOT constructively valid — its refutation side would
need excluded middle (`apart-from-P ∨ P`).  The `!` grants unrestricted access
to the joint affirmation, which suffices to refute the conjunction. -/
def bang_with_perp_bot : ！(P ⊓ Pᗮ) ⊢ AProp.bot := by antithesis

-- These De Morgan laws are definitional equalities of `.pos`/`.neg`, so the
-- entailment maps are the identity.
def compl_with : (P ⊓ Q)ᗮ ⊢ Pᗮ ⊔ Qᗮ := ⟨id, id⟩
def with_compl : Pᗮ ⊔ Qᗮ ⊢ (P ⊓ Q)ᗮ := ⟨id, id⟩

/-! ## Quantifiers -/

variable {α : Type v} {B : α → AProp.{u}}

def all_elim (a : α) : AProp.all B ⊢ B a :=
  ⟨fun f => f a, fun hn => Trunc'.mk ⟨a, hn⟩⟩

def all_intro {R : AProp.{w}} (h : ∀ x, R ⊢ B x) : R ⊢ AProp.all B :=
  ⟨fun hr x => (h x).1 hr, Trunc'.elimProp (fun p => (h p.1).2 p.2)⟩

def ex_intro (a : α) : B a ⊢ AProp.ex B :=
  ⟨fun hp => Trunc'.mk ⟨a, hp⟩, fun f => f a⟩

def ex_elim {R : AProp.{w}} (h : ∀ x, B x ⊢ R) : AProp.ex B ⊢ R :=
  ⟨Trunc'.elimProp (fun p => (h p.1).1 p.2), fun hr x => (h x).2 hr⟩

def all_mono {B B' : α → AProp.{u}} (h : ∀ x, B x ⊢ B' x) : AProp.all B ⊢ AProp.all B' :=
  all_intro fun x => cut (all_elim x) (h x)

def ex_mono {B B' : α → AProp.{u}} (h : ∀ x, B x ⊢ B' x) : AProp.ex B ⊢ AProp.ex B' :=
  ex_elim fun x => cut (h x) (ex_intro x)

/-! ## Proof-driving tactics -/

/-- `lcut B` proves `P ⊢ R` through an intermediate `B`. -/
macro "lcut " B:term : tactic => `(tactic| refine cut (Q := $B) ?_ ?_)

/-- `ldualize` reduces the goal `P ⊢ Q` to `Qᗮ ⊢ Pᗮ`. -/
macro "ldualize" : tactic => `(tactic| refine dualizeRev ?_)

/-! ## Demonstrations -/

section Demo
variable (P Q : AProp.{u}) (α : Type v) (S T : α → AProp.{u})

/-- `calc` chaining. -/
example : P ⊗ (P ⊸ Q) ⊢ Q :=
  calc P ⊗ (P ⊸ Q)
      _ ⊢ (P ⊸ Q) ⊗ P := tensor_comm
      _ ⊢ Q            := eval

/-- Predicate logic: `(⨅ x, S x ⊓ T x) ⊢ ⨅ x, S x`. -/
example : AProp.all (fun x => S x ⊓ T x) ⊢ AProp.all S :=
  all_intro fun x => cut (all_elim x) with_fst

/-- `(⨆ x, S x) ⊢ ⨆ x, (S x ⊔ T x)`. -/
example : AProp.ex S ⊢ AProp.ex (fun x => S x ⊔ T x) :=
  ex_mono fun _ => plus_inl

end Demo

end Antithesis
