/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Tactic

/-!
# The affine sequent calculus, as composable entailment rules

Every rule here is a lemma about `⊢`, proven sound against *both* components of
the Chu morphism (affirmation forward, refutation backward) once and for all.
Proofs built by composing these rules — with `Entails.trans` as cut and `calc`
for chaining — therefore handle the refutation side automatically.

The judgement is single-conclusion `Γ ⊢ B` (read `⊗Γ ⊢ B`); full classical
power is recovered when needed via `dualize` (`P ⊢ Q ↔ Qᗮ ⊢ Pᗮ`), which turns
right-hand reasoning into left-hand reasoning using the involutive negation.

These rules also form the categorical structure: `⊗` is a symmetric monoidal
bifunctor, `⊓`/`⊔` are product/coproduct, `⊸` is the internal hom, and the
quantifiers are adjoints to weakening.
-/

namespace Antithesis
open scoped Antithesis

variable {P P' Q Q' R : AProp}

/-! ## Cut and duality -/

/-- Cut / composition (also a `Trans` instance, so usable in `calc`). -/
theorem cut (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R := h₁.trans h₂

/-- Contraposition: reasoning on the right is reasoning on the left of the
dual.  This is what replaces two-sided sequents. -/
theorem dualize : (P ⊢ Q) ↔ (Qᗮ ⊢ Pᗮ) := by antithesis

theorem perp_mono (h : P ⊢ Q) : Qᗮ ⊢ Pᗮ := dualize.mp h

/-! ## Multiplicative: tensor `⊗`, par `⅋`, implication `⊸` -/

theorem tensor_mono (h₁ : P ⊢ P') (h₂ : Q ⊢ Q') : P ⊗ Q ⊢ P' ⊗ Q' := by antithesis
theorem tensor_comm : P ⊗ Q ⊢ Q ⊗ P := by antithesis
theorem tensor_assoc : (P ⊗ Q) ⊗ R ⊢ P ⊗ (Q ⊗ R) := by antithesis
theorem tensor_unit : P ⊗ AProp.top ⊢ P := by antithesis
theorem unit_tensor : P ⊢ P ⊗ AProp.top := by antithesis

/-- Affine weakening: resources may be discarded. -/
theorem tensor_weaken : P ⊗ Q ⊢ P := by antithesis

/-- Evaluation / linear modus ponens. -/
theorem eval : (P ⊸ Q) ⊗ P ⊢ Q := by antithesis

/-- The `⊗ ⊣ ⊸` adjunction (currying). -/
theorem curry (h : P ⊗ Q ⊢ R) : P ⊢ Q ⊸ R := by antithesis
theorem uncurry (h : P ⊢ Q ⊸ R) : P ⊗ Q ⊢ R := by antithesis

theorem limp_mono (h₁ : P' ⊢ P) (h₂ : Q ⊢ Q') : (P ⊸ Q) ⊢ (P' ⊸ Q') := by antithesis

/-! ## Additive: with `⊓` (product), plus `⊔` (coproduct) -/

theorem with_fst : P ⊓ Q ⊢ P := by antithesis
theorem with_snd : P ⊓ Q ⊢ Q := by antithesis
theorem with_intro (h₁ : R ⊢ P) (h₂ : R ⊢ Q) : R ⊢ P ⊓ Q := by antithesis

theorem plus_inl : P ⊢ P ⊔ Q := by antithesis
theorem plus_inr : Q ⊢ P ⊔ Q := by antithesis
theorem plus_elim (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : P ⊔ Q ⊢ R := by antithesis

/-! ## Exponential -/

/-- Dereliction `!P ⊢ P`. -/
theorem derelict : AProp.bang P ⊢ P := by antithesis

/-! ## Quantifiers (predicate logic)

`⨅`/`⨆` are right/left adjoint to weakening; these are the intro/elim rules.
The propositional solver cannot do instantiation, so these are proved by hand. -/

variable {α : Sort*} {B : α → AProp}

/-- `⨅`-elimination (instantiation at `a`). -/
theorem all_elim (a : α) : AProp.all B ⊢ B a := ⟨fun h => h a, fun hn => ⟨a, hn⟩⟩

/-- `⨅`-introduction: prove the body uniformly in a fresh variable. -/
theorem all_intro (h : ∀ x, R ⊢ B x) : R ⊢ AProp.all B :=
  ⟨fun hr x => (h x).1 hr, fun ⟨x, hx⟩ => (h x).2 hx⟩

/-- `⨆`-introduction (witness `a`). -/
theorem ex_intro (a : α) : B a ⊢ AProp.ex B := ⟨fun h => ⟨a, h⟩, fun h => h a⟩

/-- `⨆`-elimination: handle the body uniformly in a fresh variable. -/
theorem ex_elim (h : ∀ x, B x ⊢ R) : AProp.ex B ⊢ R :=
  ⟨fun ⟨x, hx⟩ => (h x).1 hx, fun hr x => (h x).2 hr⟩

theorem all_mono {B B' : α → AProp} (h : ∀ x, B x ⊢ B' x) : AProp.all B ⊢ AProp.all B' :=
  all_intro fun x => (all_elim x).trans (h x)

theorem ex_mono {B B' : α → AProp} (h : ∀ x, B x ⊢ B' x) : AProp.ex B ⊢ AProp.ex B' :=
  ex_elim fun x => (h x).trans (ex_intro x)

/-! ## Proof-driving tactics

Thin, always-sound wrappers over the rules above (each reduces to a proven
lemma, so they cannot produce an invalid proof). -/

/-- `lcut B` proves the goal `P ⊢ R` through an intermediate `B`, leaving the
two subgoals `P ⊢ B` and `B ⊢ R`. This is the cut rule as backward chaining. -/
macro "lcut " B:term : tactic => `(tactic| refine cut (Q := $B) ?_ ?_)

/-- `ldualize` contraposes the goal `P ⊢ Q` into `Qᗮ ⊢ Pᗮ`, so right-hand
reasoning becomes left-hand reasoning. -/
macro "ldualize" : tactic => `(tactic| rw [dualize])

/-! ## Demonstrations -/

section Demo
variable (P Q : AProp) (α : Sort*) (S T : α → AProp)

/-- `calc` chaining of rules (cut is the `Trans` instance). -/
example : P ⊗ (P ⊸ Q) ⊢ Q :=
  calc P ⊗ (P ⊸ Q)
      _ ⊢ (P ⊸ Q) ⊗ P := tensor_comm
      _ ⊢ Q            := eval

/-- A genuine predicate-logic entailment the solver can't do alone:
`(⨅ x, S x ⊓ T x) ⊢ (⨅ x, S x)`. -/
example : AProp.all (fun x => S x ⊓ T x) ⊢ AProp.all S :=
  all_intro fun x => (all_elim x).trans with_fst

/-- Existential distributes out of `⊔`: `(⨆ x, S x) ⊢ ⨆ x, (S x ⊔ T x)`. -/
example : AProp.ex S ⊢ AProp.ex (fun x => S x ⊔ T x) :=
  ex_mono fun _ => plus_inl

/-- Same modus ponens, driven by the `lcut` tactic instead of `calc`. -/
example : P ⊗ (P ⊸ Q) ⊢ Q := by
  lcut ((P ⊸ Q) ⊗ P)
  · exact tensor_comm
  · exact eval

/-- Using `ldualize` to attack the refutation side: `(P ⊸ Q) ⊢ (Qᗮ ⊸ Pᗮ)`
becomes, after dualizing, the structurally identical goal on the duals. -/
example : (P ⊸ Q) ⊢ (Qᗮ ⊸ Pᗮ) := by
  ldualize
  -- goal is now `(Qᗮ ⊸ Pᗮ)ᗮ ⊢ (P ⊸ Q)ᗮ`; the solver finishes the propositional core
  antithesis

end Demo

end Antithesis
