import LeanAntithesis.Math.Deriving

/-!
# The setoid algebra

Standard constructions making `AEquiv` (Bishop sets) closed under the basic
type formers, so the antithesis setoids form a usable universe:

* **products** `α × β` and **sums** `α ⊕ β` — these are plain inductives, so the
  `derive_aequiv` handler produces them (and their apartness) for free;
* the **function setoid** `α → β` — *not* inductive, built by hand: `f ~ g` is the
  universal `⨅ x, f x ~ g x`, and dually apartness `f # g` is the existential
  `⨆ x, f x # g x` ("the functions differ *somewhere*").  Reflexivity/symmetry are
  pointwise; transitivity is multiplicative, using that `⨅` commutes with `⊗`.
-/

universe u v w

namespace Antithesis
open scoped Antithesis

/-! ## Products and sums (derived) -/

derive_aequiv Prod
derive_aequiv Sum

/-! ## The function setoid

For `α` any (index) type and `β` a setoid, `α → β` is a setoid under pointwise
equivalence.  Note `α` need not itself be a setoid — this is the full function
type, not the setoid of extensional maps (that is `ASetoid.Hom`). -/

instance funAEquiv {α : Type v} {β : Type u} [AEquiv β] : AEquiv (α → β) where
  rel f g := AProp.all fun x => AEquiv.rel (f x) (g x)
  -- `Entails.of_holds` (heterogeneous in the context) lets the pointwise
  -- reflexivity sit at the `max u v` universe `all_intro` works in
  refl f := all_intro fun x => Entails.of_holds (AEquiv.refl (f x)).holds
  symm f g := all_mono fun x => AEquiv.symm (f x) (g x)
  trans f g h := cut all_tensor (all_mono fun x => AEquiv.trans (f x) (g x) (h x))

/-- Pointwise equivalence of functions is the universal of the pointwise relation. -/
theorem fun_rel {α : Type v} {β : Type u} [AEquiv β] (f g : α → β) :
    AEquiv.rel f g = AProp.all fun x => AEquiv.rel (f x) (g x) := rfl

/-- Function apartness is *pointwise apartness somewhere*: `f # g` affirms an
existential `⨆ x, f x # g x`. -/
theorem fun_apart {α : Type v} {β : Type u} [AEquiv β] (f g : α → β) :
    AEquiv.apart f g = AProp.ex fun x => AEquiv.apart (f x) (g x) :=
  AProp.ext rfl rfl

end Antithesis
