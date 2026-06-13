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

/-- Contraposition of `⊸`. -/
def limp_contra : (P ⊸ Q) ⊢ (Qᗮ ⊸ Pᗮ) := by antithesis

/-- Composition of linear implications. -/
def limp_comp : (P ⊸ Q) ⊗ (Q ⊸ R) ⊢ (P ⊸ R) :=
  ⟨fun fg => Entails.trans fg.1 fg.2,
   fun pr => ⟨fun f => ⟨f.1 pr.1, pr.2⟩, fun g => ⟨pr.1, g.2 pr.2⟩⟩⟩

/-- `⊸` distributes over `⊓` in its codomain. -/
def limp_with : (P ⊸ Q) ⊓ (P ⊸ R) ⊢ (P ⊸ (Q ⊓ R)) :=
  ⟨fun fg => ⟨fun pp => ⟨fg.1.1 pp, fg.2.1 pp⟩, Trunc'.elimProp (Sum.elim fg.1.2 fg.2.2)⟩,
   fun pr => Trunc'.elimProp (fun s =>
     Sum.elim (fun qn => Trunc'.mk (.inl ⟨pr.1, qn⟩))
              (fun rn => Trunc'.mk (.inr ⟨pr.1, rn⟩)) s) pr.2⟩

/-- `⊸` turns `⊔` in its domain into `⊓`. -/
def limp_plus : (P ⊸ R) ⊓ (Q ⊸ R) ⊢ ((P ⊔ Q) ⊸ R) :=
  ⟨fun fg => ⟨Trunc'.elimProp (Sum.elim fg.1.1 fg.2.1), fun rn => ⟨fg.1.2 rn, fg.2.2 rn⟩⟩,
   fun tr => Trunc'.elimProp (fun s =>
     Sum.elim (fun pp => Trunc'.mk (.inl ⟨pp, tr.2⟩))
              (fun qp => Trunc'.mk (.inr ⟨qp, tr.2⟩)) s) tr.1⟩

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

/-- `⨅` commutes with `⊗`. -/
def all_tensor {A B : α → AProp.{u}} :
    (AProp.all A) ⊗ (AProp.all B) ⊢ AProp.all (fun x => A x ⊗ B x) :=
  ⟨fun fg x => ⟨fg.1 x, fg.2 x⟩,
   Trunc'.elimProp fun p => ⟨fun fa => Trunc'.mk ⟨p.1, p.2.1 (fa p.1)⟩,
                             fun fb => Trunc'.mk ⟨p.1, p.2.2 (fb p.1)⟩⟩⟩

/-- `⨅` distributes over `⊓`. -/
def all_with {A B : α → AProp.{u}} :
    (AProp.all A) ⊓ (AProp.all B) ⊢ AProp.all (fun x => A x ⊓ B x) :=
  ⟨fun fg x => ⟨fg.1 x, fg.2 x⟩,
   Trunc'.elimProp fun p => Trunc'.elimProp (fun s =>
     Sum.elim (fun an => Trunc'.mk (.inl (Trunc'.mk ⟨p.1, an⟩)))
              (fun bn => Trunc'.mk (.inr (Trunc'.mk ⟨p.1, bn⟩))) s) p.2⟩

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
