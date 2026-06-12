/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.LinearTactic

/-! End-to-end tests of the `linear` proof-mode tactics. -/

namespace Antithesis
open scoped Antithesis

variable (P Q : AProp)

/-- Modus ponens: split the tensor into resources, then close. -/
example : P ⊗ (P ⊸ Q) ⊢ Q := by
  linear
  lintro hp hpq
  lclose

-- The delaborator renders the reflected context as a readable sequent.
/--
trace: P Q : AProp
⊢ ❲ hp : P, hpq : P ⊸ Q ⊢ₗ Q ❳
-/
#guard_msgs in
example : P ⊗ (P ⊸ Q) ⊢ Q := by
  linear
  lintro hp hpq
  trace_state
  lclose

/-- Affine weakening: introduce both resources, discard one, close. -/
example : P ⊗ Q ⊢ P := by
  linear
  lintro hp hq
  lweaken hq
  lclose

section Predicate
variable {α : Sort*} (S T : α → AProp) (a : α)

/-- `⨅`-instantiation. -/
example : AProp.all S ⊢ S a := by
  linear
  lintro h
  lspecialize h a
  lclose

/-- `⨆`-introduction with a witness. -/
example : S a ⊢ AProp.ex S := by
  linear
  lintro h
  lexists a
  lclose

/-- A combined one: from `(⨅ x, S x) ⊗ (⨅ x, S x ⊸ T x)` derive `T a`. -/
example : (AProp.all S) ⊗ (AProp.all (fun x => S x ⊸ T x)) ⊢ T a := by
  linear
  lintro hs hst
  lspecialize hs a
  lspecialize hst a
  lclose

end Predicate

end Antithesis
