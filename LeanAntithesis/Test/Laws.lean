/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Logic.Tactic

/-! Regression tests / demos for the `antithesis` solver (Type-valued). -/

namespace Antithesis
open scoped Antithesis

variable (P Q R : AProp)

-- Preorder
example : P ⊢ P := by antithesis

-- Additive projections / injections
example : P ⊓ Q ⊢ P := by antithesis
example : P ⊓ Q ⊢ Q := by antithesis
example : P ⊢ P ⊔ Q := by antithesis
example : Q ⊢ P ⊔ Q := by antithesis

-- Multiplicative weakening (affine)
example : P ⊗ Q ⊢ P := by antithesis
example : P ⊗ Q ⊢ Q := by antithesis

-- Tensor/par symmetry
example : P ⊗ Q ⊢ Q ⊗ P := by antithesis
example : P ⅋ Q ⊢ Q ⅋ P := by antithesis

-- Exponentials
example : ！P ⊢ P := by antithesis
example : P ⊢ ？P := by antithesis

-- De Morgan, both directions
example : (P ⊗ Q)ᗮ ⊢ Pᗮ ⅋ Qᗮ := by antithesis
example : Pᗮ ⅋ Qᗮ ⊢ (P ⊗ Q)ᗮ := by antithesis
example : (P ⊓ Q)ᗮ ⊢ Pᗮ ⊔ Qᗮ := by antithesis
example : Pᗮ ⊔ Qᗮ ⊢ (P ⊓ Q)ᗮ := by antithesis

-- Distributivity of ⊗ over ⊔ — valid because components are subsingletons,
-- so a truncated disjunction eliminates into them (`Trunc'.elimProp`).
example : P ⊗ (Q ⊔ R) ⊢ (P ⊗ Q) ⊔ (P ⊗ R) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hp, t⟩
    refine Trunc'.elimProp (fun s => ?_) t
    rcases s with hq | hr
    · exact Trunc'.mk (.inl ⟨hp, hq⟩)
    · exact Trunc'.mk (.inr ⟨hp, hr⟩)
  · rintro ⟨⟨pq1, pq2⟩, ⟨pr1, pr2⟩⟩
    exact ⟨fun hp => ⟨pq1 hp, pr1 hp⟩, Trunc'.elimProp (Sum.elim pq2 pr2)⟩

-- Contraposition; modus ponens as a tensor
example : P ⊸ Q ⊢ Qᗮ ⊸ Pᗮ := by antithesis
example : P ⊗ (P ⊸ Q) ⊢ Q := by antithesis

end Antithesis
