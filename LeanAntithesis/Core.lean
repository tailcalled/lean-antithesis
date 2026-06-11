/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import Mathlib.Tactic.Common

/-!
# The antithesis interpretation: core type

Following Mike Shulman, *Affine logic for constructive mathematics*
(arXiv:1805.07518), and the nLab page "antithesis interpretation".

An affine proposition is interpreted in intuitionistic logic as a pair of
ordinary propositions: an **affirmation** `pos` (written `P⁺`) and a
**refutation** `neg` (written `P⁻`), which are *mutually exclusive*:
`¬(pos ∧ neg)`.

We use the curried form `pos → neg → False` for `excl`, which is logically
equivalent to `¬(pos ∧ neg)` but more convenient to apply.
-/

namespace Antithesis

/-- An affine proposition in the antithesis interpretation: an affirmation
`pos` and a refutation `neg`, which cannot both hold.

This is the type `Ω± = Σ (P⁺ : Ω) (P⁻ : Ω), ¬(P⁺ ∧ P⁻)`. -/
structure AProp : Type where
  /-- Evidence *for* the proposition (`P⁺`). -/
  pos : Prop
  /-- Evidence *against* the proposition (`P⁻`). -/
  neg : Prop
  /-- The affirmation and refutation are mutually exclusive. -/
  excl : pos → neg → False

namespace AProp

/-- Apply the exclusivity proof in `¬(pos ∧ neg)` form. -/
theorem not_and (P : AProp) : ¬(P.pos ∧ P.neg) := fun ⟨h₁, h₂⟩ => P.excl h₁ h₂

/-- Two affine propositions are equal once their affirmations and refutations
agree (the exclusivity proof is a `Prop` and hence irrelevant). -/
@[ext]
theorem ext {P Q : AProp} (hpos : P.pos = Q.pos) (hneg : P.neg = Q.neg) : P = Q := by
  cases P; cases Q; subst hpos; subst hneg; rfl

end AProp

end Antithesis
