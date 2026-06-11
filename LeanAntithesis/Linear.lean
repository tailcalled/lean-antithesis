/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Calculus

/-!
# A proof mode for affine logic: the reflected linear context

This is the data layer for the `linear` tactic block.  A proof state carries a
**named context** of affine resources together with a single conclusion; it is
reflected as the proposition `Seq Γ G` where `Γ : LCtx` is a list of
`(name, resource)` pairs and `G : AProp` is the goal.

`Seq Γ G` means `(⊗Γ) ⊢ G`, the tensor of all resources entailing the goal.
Every proof step is one of the directional lemmas below — each a one-liner over
the calculus rules in `Calculus.lean`, hence sound, handling *both* Chu maps.
The tactics in `Tactic/Linear.lean` simply `refine` these lemmas while keeping
the names in sync.

Names are stored as `String` literals inside the term so they survive between
tactic calls; a delaborator renders `Seq` as a familiar hypothesis list.
-/

namespace Antithesis
open scoped Antithesis

namespace Linear

/-- A named affine context: a list of `(name, resource)` pairs. -/
inductive LCtx where
  | nil : LCtx
  | cons (name : String) (res : AProp) (rest : LCtx) : LCtx

/-- Interpret a context as the tensor of its resources (right-nested, with the
tensor unit at the end). -/
def LCtx.interp : LCtx → AProp
  | .nil => AProp.top
  | .cons _ A Γ => A ⊗ Γ.interp

/-- The linear sequent judgement: the resources `Γ` affinely entail `G`. -/
def Seq (Γ : LCtx) (G : AProp) : Prop := Γ.interp ⊢ G

/-! ## Directional rules (what the tactics apply)

Each lemma reduces a goal on the right to a goal on the left, so the tactic
proves it by `refine rule ?_`. -/

variable {Γ : LCtx} {A B G : AProp} {n n₁ n₂ : String}

/-- `linear` entry: a bare entailment is a one-resource sequent. -/
theorem Seq.ofEntails (h : Seq (.cons n A .nil) G) : A ⊢ G :=
  cut unit_tensor h

/-- `lintro` splitting a tensor resource (⊗-left): name its two components. -/
theorem Seq.split (h : Seq (.cons n₁ A (.cons n₂ B Γ)) G) :
    Seq (.cons n (A ⊗ B) Γ) G :=
  cut tensor_assoc h

/-- `lintro` on a `⊸` goal (⊸-right): move the premise in as a named resource. -/
theorem Seq.introLimp (h : Seq (.cons n A Γ) B) : Seq Γ (A ⊸ B) :=
  curry (cut tensor_comm h)

/-- `lspecialize`/`lintro` instantiating a `⨅` resource at `a` (∀-left). -/
theorem Seq.specialize {α : Sort*} {P : α → AProp} (a : α)
    (h : Seq (.cons n (P a) Γ) G) : Seq (.cons n (AProp.all P) Γ) G :=
  cut (tensor_mono (all_elim a) (Entails.refl _)) h

/-- `lexists` providing a witness for a `⨆` goal (∃-right). -/
theorem Seq.exists_intro {α : Sort*} {P : α → AProp} (a : α)
    (h : Seq Γ (P a)) : Seq Γ (AProp.ex P) :=
  cut h (ex_intro a)

/-- `lweaken`: discard the head resource (affine weakening). -/
theorem Seq.weaken (h : Seq Γ G) : Seq (.cons n A Γ) G :=
  cut (cut tensor_comm tensor_weaken) h

/-- Closing the goal: reduce `Seq Γ G` to the underlying entailment, to be
discharged by the propositional solver. -/
theorem Seq.close (h : Γ.interp ⊢ G) : Seq Γ G := h

/-- Reshape the context to any `Γ'` whose tensor is entailed by the current
one — covers reassociation (`lintro` splitting), reordering (`lexchange`), and
dropping (`lweaken`).  The side condition is propositional, so the solver
proves it automatically. -/
theorem Seq.changeCtx {Γ Γ' : LCtx} {G : AProp}
    (reassoc : Γ.interp ⊢ Γ'.interp) (h : Seq Γ' G) : Seq Γ G :=
  cut reassoc h

/-! ## Validation

These are exactly the proof skeletons the `linear` tactic will generate: a
chain of `refine`s through the rules above, closed by `antithesis`. -/

section Validate
variable (P Q : AProp)

/-- `linear; lintro hp hpq; lexact hpq hp` will elaborate to this. -/
example : P ⊗ (P ⊸ Q) ⊢ Q :=
  Seq.ofEntails (n := "h") <|
    Seq.split (n := "h") (n₁ := "hp") (n₂ := "hpq") <|
      Seq.close (by simp only [LCtx.interp]; antithesis)

/-- `linear; lintro h; lspecialize h a; lexact h` will elaborate to this. -/
example {α : Sort*} (S : α → AProp) (a : α) : AProp.all S ⊢ S a :=
  Seq.ofEntails (n := "h") <|
    Seq.specialize (n := "h") a <|
      Seq.close (by simp only [LCtx.interp]; antithesis)

end Validate

end Linear
end Antithesis
