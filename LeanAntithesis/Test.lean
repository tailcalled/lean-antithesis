/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Tactic

/-! Regression tests / demos for the `antithesis` tactic.  Every law here is
intuitionistically valid in affine logic. -/

namespace Antithesis
open scoped Antithesis

variable (P Q R : AProp)

-- Preorder
example : P ⊢ P := by antithesis

-- Additive projections (with)
example : P ⊓ Q ⊢ P := by antithesis
example : P ⊓ Q ⊢ Q := by antithesis

-- Additive injections (plus)
example : P ⊢ P ⊔ Q := by antithesis
example : Q ⊢ P ⊔ Q := by antithesis

-- Multiplicative weakening (affine!) — needs atom exclusivity
example : P ⊗ Q ⊢ P := by antithesis
example : P ⊗ Q ⊢ Q := by antithesis

-- Tensor/par symmetry
example : P ⊗ Q ⊢ Q ⊗ P := by antithesis
example : P ⅋ Q ⊢ Q ⅋ P := by antithesis

-- Exponentials: dereliction and its dual
example : ！P ⊢ P := by antithesis
example : P ⊢ ？P := by antithesis

-- De Morgan dualities, both directions, via entailment
example : (P ⊗ Q)ᗮ ⊢ Pᗮ ⅋ Qᗮ := by antithesis
example : Pᗮ ⅋ Qᗮ ⊢ (P ⊗ Q)ᗮ := by antithesis
example : (P ⊓ Q)ᗮ ⊢ Pᗮ ⊔ Qᗮ := by antithesis
example : Pᗮ ⊔ Qᗮ ⊢ (P ⊓ Q)ᗮ := by antithesis

-- Linear distributivity of ⊗ over ⊔
example : P ⊗ (Q ⊔ R) ⊢ (P ⊗ Q) ⊔ (P ⊗ R) := by antithesis

-- Contraposition of linear implication
example : P ⊸ Q ⊢ Qᗮ ⊸ Pᗮ := by antithesis

-- Modus ponens as a tensor: P ⊗ (P ⊸ Q) ⊢ Q
example : P ⊗ (P ⊸ Q) ⊢ Q := by antithesis

end Antithesis
