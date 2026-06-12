import LeanAntithesis.Logic.Calculus
import Mathlib.Order.SetNotation

/-!
# Complemented subsets

A **complemented subset** of `X` (Shulman: the antithesis of a subset) is a map
`X → AProp`: to each point it assigns affirming evidence of *membership* and
refuting evidence of *apartness from the set*, mutually exclusive.

The Boolean-algebra-like structure is the affine connectives applied pointwise:
intersection is `⊓`, union is `⊔`, complement is `ᗮ`, inclusion `S ⊑ T` is
pointwise entailment.  Every law is *definitionally* a connective law, so the
proofs are one-liners over the calculus.

Being `Type`-valued, membership `x ∈ₐ S` is a *type of witnesses*, not a truth
value.
-/

universe u v

namespace Antithesis
open scoped Antithesis

/-- A complemented subset of `X`. -/
def CSet (X : Type v) : Type (max (u + 1) v) := X → AProp.{u}

namespace CSet
variable {X : Type v} (S T U : CSet.{u} X) (x : X)

/-- Membership witnesses at `x`. -/
def Mem : Type u := (S x).pos
/-- Apartness-from-`S` witnesses at `x`. -/
def Apart : Type u := (S x).neg

@[inherit_doc] scoped notation:50 x " ∈ₐ " S => CSet.Mem S x
@[inherit_doc] scoped notation:50 x " ⋕ " S => CSet.Apart S x

/-- Membership and apartness exclude each other. -/
def mem_apart_excl : (x ∈ₐ S) → (x ⋕ S) → Empty := (S x).excl

/-! ## Operations (pointwise affine connectives) -/

instance : Inter (CSet.{u} X) := ⟨fun S T x => S x ⊓ T x⟩
instance : Union (CSet.{u} X) := ⟨fun S T x => S x ⊔ T x⟩
instance : Compl (CSet.{u} X) := ⟨fun S x => (S x)ᗮ⟩
instance : EmptyCollection (CSet.{u} X) := ⟨fun _ => AProp.bot⟩

/-- The full subset. -/
def univ : CSet.{u} X := fun _ => AProp.top

/-- Multiplicative intersection (tensor). -/
def tinter (S T : CSet.{u} X) : CSet.{u} X := fun x => S x ⊗ T x
/-- Multiplicative union (par). -/
def tunion (S T : CSet.{u} X) : CSet.{u} X := fun x => S x ⅋ T x

/-- Inclusion: pointwise entailment (a transformation of witnesses). -/
def Subset (S T : CSet.{u} X) : Type (max u v) := ∀ x, S x ⊢ T x

@[inherit_doc] scoped infix:50 " ⊑ " => CSet.Subset

/-! ## Laws — each is definitionally a connective law -/

variable {S T U}

/-- Inclusion is reflexive. -/
def Subset.refl : S ⊑ S := fun _ => Entails.refl _
/-- Inclusion is transitive. -/
def Subset.trans (h₁ : S ⊑ T) (h₂ : T ⊑ U) : S ⊑ U := fun x => cut (h₁ x) (h₂ x)

/-- Complement is involutive. -/
@[simp] theorem compl_compl : Sᶜᶜ = S := rfl

/-- The empty subset is included in everything; everything in the full subset. -/
def empty_subset : (∅ : CSet.{u} X) ⊑ S := fun _ => bot_entails
def subset_univ : S ⊑ univ := fun _ => entails_top

/-- Intersection projects; union injects. -/
def inter_subset_left : S ∩ T ⊑ S := fun _ => with_fst
def inter_subset_right : S ∩ T ⊑ T := fun _ => with_snd
def subset_union_left : S ⊑ S ∪ T := fun _ => plus_inl
def subset_union_right : T ⊑ S ∪ T := fun _ => plus_inr

/-- Universal properties of `∩` and `∪`. -/
def subset_inter (h₁ : U ⊑ S) (h₂ : U ⊑ T) : U ⊑ S ∩ T := fun x => with_intro (h₁ x) (h₂ x)
def union_subset (h₁ : S ⊑ U) (h₂ : T ⊑ U) : S ∪ T ⊑ U := fun x => plus_elim (h₁ x) (h₂ x)

/-- Contraposition: inclusion reverses under complement. -/
def compl_subset_compl (h : S ⊑ T) : Tᶜ ⊑ Sᶜ := fun x => perp_mono (h x)

/-- Pointwise exponential `!S` (unrestricted access). -/
def bang (S : CSet.{u} X) : CSet.{u} X := fun x => ！(S x)

/-- With the exponential, a complemented subset is disjoint from its complement:
`!(S ∩ Sᶜ) ⊑ ∅`.  (The bare `S ∩ Sᶜ ⊑ ∅` would need excluded middle; `!` is what
makes the disjointness expressible *inside* the affine logic.) -/
def bang_inter_compl_subset_empty : (S ∩ Sᶜ).bang ⊑ (∅ : CSet.{u} X) :=
  fun _ => bang_with_perp_bot

/-- De Morgan, both directions. -/
def compl_inter : (S ∩ T)ᶜ ⊑ Sᶜ ∪ Tᶜ := fun _ => compl_with
def union_compl_subset : Sᶜ ∪ Tᶜ ⊑ (S ∩ T)ᶜ := fun _ => with_compl

end CSet
end Antithesis
