/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Tactic

/-!
# Examples

Two things are demonstrated here:

1. the surface syntax `⟬ ⟭` and the `antithesis` tactic on concrete formulas;
2. Shulman's headline phenomenon — **apartness is the antithesis of
   equality** — packaged as: the refutation side of any affine equivalence
   relation is automatically an irreflexive, symmetric relation satisfying a
   substitution (weak cotransitivity) law.
-/

namespace Antithesis
open scoped Antithesis

/-! ## Surface syntax -/

section Surface
variable (P Q R : AProp) (p q : Prop)

-- The brackets translate to the named connectives, definitionally.
example : ⟬ P ⊗ Q ⟭ = P.tensor Q := rfl
example : ⟬ P ⊓ Q ⊸ R ⟭ = (P.with' Q).limp R := rfl
example : ⟬ ~ P ⟭ = P.perp := rfl
example : ⟬ P ᗮ ⟭ = P.perp := rfl

-- Atoms: an `AProp` is embedded directly; a `Prop` is lifted to `(p, ¬p)`.
example : ⟬ ⟪p⟫ ⟭ = AProp.lift p := rfl
example : ⟬ P ⊗ ⟪p⟫ ⟭ = P.tensor (AProp.lift p) := rfl

-- Quantifiers bind a Lean variable; the body is affine.
example (A : Prop) (S : A → AProp) :
    ⟬ ∀ a, ⟪A⟫ ⊸ ⟪S a⟫ ⟭ = AProp.all (fun a => (AProp.lift A).limp (S a)) := rfl

-- ...and the tactic proves entailments stated in surface syntax:
example : ⟬ P ⊗ Q ⟭ ⊢ ⟬ Q ⊗ P ⟭ := by antithesis
example : ⟬ ⟪p⟫ ⊓ ⟪q⟫ ⟭ ⊢ ⟬ ⟪p⟫ ⟭ := by antithesis

end Surface

/-! ## Apartness as the antithesis of equality

An **affine equivalence relation** assigns to each pair an affine proposition
that is reflexive, symmetric, and (multiplicatively) transitive. -/

/-- An affine (proof-irrelevant) equivalence relation on `α`. -/
structure AEquiv (α : Type*) where
  /-- The affine relation; `(rel x y)⁺` asserts `x ~ y`, `(rel x y)⁻` refutes it. -/
  rel : α → α → AProp
  refl : ∀ x, Holds (rel x x)
  symm : ∀ x y, rel x y ⊢ rel y x
  trans : ∀ x y z, rel x y ⊗ rel y z ⊢ rel x z

namespace AEquiv
variable {α : Type*} (E : AEquiv α)

/-- The **apartness** induced by an affine equivalence relation: the refutation
side `x # y := (x ~ y)⁻`. -/
def apart (x y : α) : Prop := (E.rel x y).neg

/-- Apartness is irreflexive — the antithesis of reflexivity. -/
theorem apart_irrefl (x : α) : ¬ E.apart x x := (E.rel x x).excl (E.refl x)

/-- Apartness is symmetric — the antithesis of symmetry. -/
theorem apart_symm {x y : α} (h : E.apart x y) : E.apart y x := (E.symm y x).2 h

/-- Substitution / weak cotransitivity — the antithesis of transitivity: if
`x # z`, then `x ~ y` forces `y # z`, and `y ~ z` forces `x # y`. -/
theorem apart_subst {x y z : α} (h : E.apart x z) :
    (Holds (E.rel x y) → E.apart y z) ∧ (Holds (E.rel y z) → E.apart x y) :=
  (E.trans x y z).2 h

end AEquiv

/-- The discrete affine equivalence relation `x ↦ (x = y, x ≠ y)` on any type;
here the induced apartness is just `≠`. -/
def eqAEquiv (α : Type*) : AEquiv α where
  rel x y := AProp.lift (x = y)
  refl _ := rfl
  symm _ _ := ⟨Eq.symm, fun hne h => hne h.symm⟩
  trans _ _ _ :=
    ⟨fun ⟨a, b⟩ => a.trans b,
     fun hne => ⟨fun hxy hyz => hne (hxy.trans hyz), fun hyz hxy => hne (hxy.trans hyz)⟩⟩

example (α : Type*) (x : α) : ¬ (eqAEquiv α).apart x x := (eqAEquiv α).apart_irrefl x

end Antithesis
