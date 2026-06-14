import LeanAntithesis.Sets.Deriving

/-!
# The setoid algebra

Standard constructions making `AEquiv` (Bishop sets) closed under the basic
type formers, so the antithesis setoids form a usable universe:

* **products** `α × β` and **sums** `α ⊕ β` — these are plain inductives, so the
  `derive_aequiv` handler produces them (and their apartness) for free.  The derived
  `α × β` is the **cartesian product** in the category of setoids: it has projections
  and a pairing with the universal property (`ASetoid.prod`/`fst`/`snd`/`pair`);
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

/-! ## The cartesian product of setoids

The derived `α × β` is additive (related in both coordinates, apart in some
coordinate), which is exactly the categorical product: projections plus a pairing
`with_intro`-style, with the universal property. -/

namespace ASetoid

/-- The product setoid `X × Y`, using the derived `AEquiv` on the carrier product. -/
def prod (X Y : ASetoid.{u}) : ASetoid.{u} :=
  letI := X.eqv; letI := Y.eqv; .of (X.carrier × Y.carrier)

variable {X Y Z : ASetoid.{u}}

/-- First projection. -/
def fst : Hom (X.prod Y) X :=
  letI := X.eqv; letI := Y.eqv
  ⟨Prod.fst, fun _ _ => ⟨Trunc'.elimProp fun h => match h with | .mk hp _ => hp,
                          fun hn => Trunc'.mk (.mk_0 hn)⟩⟩

/-- Second projection. -/
def snd : Hom (X.prod Y) Y :=
  letI := X.eqv; letI := Y.eqv
  ⟨Prod.snd, fun _ _ => ⟨Trunc'.elimProp fun h => match h with | .mk _ hp => hp,
                          fun hn => Trunc'.mk (.mk_1 hn)⟩⟩

/-- Pairing — the universal map. -/
def pair (f : Hom Z X) (g : Hom Z Y) : Hom Z (X.prod Y) :=
  letI := X.eqv; letI := Y.eqv
  ⟨fun z => (f.toFun z, g.toFun z),
   fun z z' => ⟨fun h => Trunc'.mk (.mk ((f.resp z z').1 h) ((g.resp z z').1 h)),
     Trunc'.elimProp fun a => match a with
       | .mk_0 hn => (f.resp z z').2 hn
       | .mk_1 hn => (g.resp z z').2 hn⟩⟩

/-- Universal property of the product: `pair` factors the projections, uniquely. -/
@[simp] theorem fst_pair (f : Hom Z X) (g : Hom Z Y) : fst.comp (pair f g) = f := Hom.ext rfl
@[simp] theorem snd_pair (f : Hom Z X) (g : Hom Z Y) : snd.comp (pair f g) = g := Hom.ext rfl
theorem pair_unique (h : Hom Z (X.prod Y)) :
    pair (fst.comp h) (snd.comp h) = h := Hom.ext rfl

end ASetoid

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
