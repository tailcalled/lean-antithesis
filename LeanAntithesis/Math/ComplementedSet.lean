import LeanAntithesis.Logic.Calculus
import Mathlib.Order.SetNotation

/-!
# Complemented subsets

A **complemented subset** of `X` (Shulman: the antithesis of a subset) is a map
`X → AProp`: to each point it assigns affirming evidence of *membership* and
refuting evidence of *apartness from the set*, mutually exclusive.

The Boolean-algebra-like structure is the affine connectives applied pointwise:
intersection is `⊓`, union is `⊔`, complement is `ᗮ`.  **Inclusion** `S ⊑ T` is
itself an affine proposition — `⨅ x, S x ⊸ T x` — so it has both sides.  Its
validity is stated as the sequent `Valid (S ⊑ T) = 𝟙 ⊢ S ⊑ T` (which composes via
`cut`, unlike a bare `Holds`); its refutation `(S ⊑ T)ᗮ` is a witness of
*non-inclusion* (a member of `S` apart from `T`).  Every law is *definitionally*
a connective law, so the proofs are one-liners over the calculus.

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

/-- Inclusion, as an affine proposition: `S ⊑ T = ⨅ x, S x ⊸ T x`.  Affirmation
is pointwise entailment; refutation is a member of `S` apart from `T`. -/
def Subset (S T : CSet.{u} X) : AProp.{max u v} := AProp.all (fun x => S x ⊸ T x)

@[inherit_doc] scoped infix:50 " ⊑ " => CSet.Subset

variable {S T U}

/-- An inclusion `𝟙 ⊢ S ⊑ T` from pointwise entailments. -/
def Subset.mk (h : ∀ x, S x ⊢ T x) : Valid (S ⊑ T) := Valid.of_holds h
/-- Use an inclusion pointwise. -/
def Subset.app (h : Valid (S ⊑ T)) (x : X) : S x ⊢ T x := Valid.holds h x

/-- A non-inclusion `𝟙 ⊢ (S ⊑ T)ᗮ`: a member of `S` apart from `T`. -/
def not_subset (x : X) (hx : x ∈ₐ S) (hx' : x ⋕ T) : Valid ((S ⊑ T)ᗮ) :=
  ⟨fun _ => Trunc'.mk ⟨x, hx, hx'⟩, fun f => ((T x).excl ((f x).1 hx) hx').elim⟩

/-! ## Laws — sequents that compose via `cut`/the calculus -/

/-- Inclusion is reflexive. -/
def subset_refl : Valid (S ⊑ S) := Subset.mk fun _ => Entails.refl _
/-- Inclusion is transitive — a multiplicative sequent, composing via `cut`. -/
def subset_trans : (S ⊑ T) ⊗ (T ⊑ U) ⊢ (S ⊑ U) :=
  cut all_tensor (all_mono fun _ => limp_comp)

/-- Complement is involutive. -/
@[simp] theorem compl_compl : Sᶜᶜ = S := rfl

/-- The empty subset is included in everything; everything in the full subset. -/
def empty_subset : Valid ((∅ : CSet.{u} X) ⊑ S) := Subset.mk fun _ => bot_entails
def subset_univ : Valid (S ⊑ univ) := Subset.mk fun _ => entails_top

/-- Intersection projects; union injects. -/
def inter_subset_left : Valid (S ∩ T ⊑ S) := Subset.mk fun _ => with_fst
def inter_subset_right : Valid (S ∩ T ⊑ T) := Subset.mk fun _ => with_snd
def subset_union_left : Valid (S ⊑ S ∪ T) := Subset.mk fun _ => plus_inl
def subset_union_right : Valid (T ⊑ S ∪ T) := Subset.mk fun _ => plus_inr

/-- Universal properties of `∩` and `∪`, as sequents (the premises are combined
additively, `⊓`, so they compose in any context). -/
def subset_inter : (U ⊑ S) ⊓ (U ⊑ T) ⊢ (U ⊑ S ∩ T) :=
  cut all_with (all_mono fun _ => limp_with)
def union_subset : (S ⊑ U) ⊓ (T ⊑ U) ⊢ (S ∪ T ⊑ U) :=
  cut all_with (all_mono fun _ => limp_plus)

/-- Contraposition: inclusion reverses under complement. -/
def compl_subset_compl : (S ⊑ T) ⊢ (Tᶜ ⊑ Sᶜ) :=
  all_mono fun _ => limp_contra

/-- Pointwise exponential `!S` (unrestricted access). -/
def bang (S : CSet.{u} X) : CSet.{u} X := fun x => ！(S x)

/-- With the exponential, a complemented subset is disjoint from its complement:
`!(S ∩ Sᶜ) ⊑ ∅`.  (The bare `S ∩ Sᶜ ⊑ ∅` would need excluded middle; `!` is what
makes the disjointness expressible *inside* the affine logic.) -/
def bang_inter_compl_subset_empty : Valid ((S ∩ Sᶜ).bang ⊑ (∅ : CSet.{u} X)) :=
  Subset.mk fun _ => bang_with_perp_bot

/-- De Morgan, both directions. -/
def compl_inter : Valid ((S ∩ T)ᶜ ⊑ Sᶜ ∪ Tᶜ) := Subset.mk fun _ => compl_with
def union_compl_subset : Valid (Sᶜ ∪ Tᶜ ⊑ (S ∩ T)ᶜ) := Subset.mk fun _ => with_compl

end CSet
end Antithesis
