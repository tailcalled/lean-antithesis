import LeanAntithesis.Logic.Lift

/-!
# Surface syntax for affine formulas

`⟬ φ ⟭` translates an affine formula `φ`, written in a dedicated grammar, into
an `AProp`.  Inside the brackets:

* `⊗ ⅋` are multiplicative conjunction/disjunction (tensor, par);
* `⊓ ⊔` (or `&` / `⊕`) are additive conjunction/disjunction (with, plus);
* `⊸` is linear implication; `~ φ` / `φ ᗮ` is linear negation;
* `! φ` / `? φ` are the exponentials;
* `⊤ ⊥` are the units; `∀ x, φ` / `∃ x, φ` are the linear quantifiers;
* a bare identifier or `⟪ e ⟫` embeds a Lean term: if it is already an `AProp`
  it is used directly, if it is a `Prop` it is lifted via `AProp.lift`.

Example: `⟬ ∀ x, ⟪P x⟫ ⊗ Q ⊸ ⟪x = y⟫ ⟭`.
-/

namespace Antithesis
open Lean

universe u v

/-- Coercion of a Lean value into an `AProp`: an `AProp` is itself; a `Prop` is
lifted.  This is what atom positions in `⟬ ⟭` elaborate through. -/
class ToAProp (α : Sort v) where
  /-- Interpret `a` as an affine proposition. -/
  toAProp : α → AProp.{u}

instance : ToAProp (AProp.{u}) := ⟨fun P => P⟩
instance : ToAProp Prop := ⟨AProp.liftProp⟩

@[simp] theorem toAProp_aprop (P : AProp.{u}) : (ToAProp.toAProp P : AProp.{u}) = P := rfl
@[simp] theorem toAProp_prop (p : Prop) : (ToAProp.toAProp p : AProp.{0}) = AProp.liftProp p := rfl

/-! ## The `aprop` grammar -/

declare_syntax_cat aprop

-- atoms / leaves
syntax:max "(" aprop ")" : aprop
syntax:max "⊤" : aprop
syntax:max "⊥" : aprop
syntax:max "⟪" term "⟫" : aprop
syntax:max ident : aprop

-- unary, tightest
syntax:90 "~" aprop:90 : aprop
syntax:90 "!" aprop:90 : aprop
syntax:90 "?" aprop:90 : aprop
syntax:91 aprop:91 "ᗮ" : aprop

-- binary connectives (left associative); ⊗ tighter than ⅋ tighter than ⊓/⊔
syntax:65 aprop:66 " ⊗ " aprop:65 : aprop
syntax:64 aprop:65 " ⅋ " aprop:64 : aprop
syntax:63 aprop:64 " ⊓ " aprop:63 : aprop
syntax:63 aprop:64 " & " aprop:63 : aprop
syntax:62 aprop:63 " ⊔ " aprop:62 : aprop
syntax:62 aprop:63 " ⊕ " aprop:62 : aprop

-- implication, right associative, looser than the conjunctions/disjunctions
syntax:50 aprop:51 " ⊸ " aprop:50 : aprop

-- quantifiers, loosest, extend to the right
syntax:10 "∀ " explicitBinders ", " aprop:10 : aprop
syntax:10 "∃ " explicitBinders ", " aprop:10 : aprop

/-- Entry point: interpret an affine formula as an `AProp`. -/
syntax:max "⟬" aprop "⟭" : term

macro_rules
  | `(⟬ ($p) ⟭)      => `(⟬ $p ⟭)
  | `(⟬ ⊤ ⟭)         => `(AProp.top)
  | `(⟬ ⊥ ⟭)         => `(AProp.bot)
  | `(⟬ ⟪ $e ⟫ ⟭)   => `(ToAProp.toAProp $e)
  | `(⟬ $x:ident ⟭)  => `(ToAProp.toAProp $x)
  | `(⟬ ~ $p ⟭)      => `(AProp.perp ⟬ $p ⟭)
  | `(⟬ $p ᗮ ⟭)      => `(AProp.perp ⟬ $p ⟭)
  | `(⟬ ! $p ⟭)      => `(AProp.bang ⟬ $p ⟭)
  | `(⟬ ? $p ⟭)      => `(AProp.quest ⟬ $p ⟭)
  | `(⟬ $p ⊗ $q ⟭)  => `(AProp.tensor ⟬ $p ⟭ ⟬ $q ⟭)
  | `(⟬ $p ⅋ $q ⟭)  => `(AProp.par ⟬ $p ⟭ ⟬ $q ⟭)
  | `(⟬ $p ⊓ $q ⟭)  => `(AProp.with' ⟬ $p ⟭ ⟬ $q ⟭)
  | `(⟬ $p & $q ⟭)  => `(AProp.with' ⟬ $p ⟭ ⟬ $q ⟭)
  | `(⟬ $p ⊔ $q ⟭)  => `(AProp.plus ⟬ $p ⟭ ⟬ $q ⟭)
  | `(⟬ $p ⊕ $q ⟭)  => `(AProp.plus ⟬ $p ⟭ ⟬ $q ⟭)
  | `(⟬ $p ⊸ $q ⟭)  => `(AProp.limp ⟬ $p ⟭ ⟬ $q ⟭)
  | `(⟬ ∀ $xs:explicitBinders, $p ⟭) => do
      Lean.expandExplicitBinders ``AProp.all xs (← `(⟬ $p ⟭))
  | `(⟬ ∃ $xs:explicitBinders, $p ⟭) => do
      Lean.expandExplicitBinders ``AProp.ex xs (← `(⟬ $p ⟭))

end Antithesis
