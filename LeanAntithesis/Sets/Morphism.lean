import LeanAntithesis.Sets.Discrete

/-!
# Congruences and deriving morphisms from pointful expressions

**Congruence typeclasses** carry, per operation, the witness that it *respects*
the affine equivalence (the antithesis analogue of Coq's `Proper`/`Morphisms`).
A unary op `f` needs `a ~ a' ⊢ f a ~ f a'`; a binary op `⊕` needs the **additive**
form `a ~ a' ⊓ b ~ b' ⊢ (a ⊕ b) ~ (a' ⊕ b')`, whose apartness side
`a ⊕ b # a' ⊕ b' → a # a' ∨ b # b'` is **strong extensionality** — the standard
constructive (Bishop) condition on operations.  For a **discrete** set every
operation qualifies, so `discrete.cong*` populate the instances for free.

`CoeFun` lets a morphism be applied like a function, and the **`mor` tactic**
fills in `resp` for a pointfully-written `toFun`:

* on a discrete domain `discrete.resp` closes it in one shot (infix arithmetic,
  polynomials, anything);
* otherwise it peels the expression — named morphisms (`homApp`), unary
  congruences (`negApp`), and **binary** congruences (`addApp`/`subApp`/`mulApp`),
  bottoming at the variable (`Entails.refl`) or a constant (`homConst`).

A binary op on a *shared* variable `fun x => f x ⊕ g x` is fine: the two sub-proofs
are paired with `with_intro` — the **cartesian** pairing, needing *no contraction* —
then the strongly-extensional congruence is applied.  (The multiplicative `⊗` form
would need contraction and is the wrong shape.)
-/

namespace Antithesis
open scoped Antithesis

/-! ## Congruence typeclasses -/

variable {α : Type}

/-- Every unary function respects discrete equality. -/
def discrete.cong₁ (f : α → α) {a a' : α} :
    (discrete α).rel a a' ⊢ (discrete α).rel (f a) (f a') := discrete.resp f a a'

/-- Every binary operation respects discrete equality (additive form / strong
extensionality).  The apartness side uses decidability of `=`. -/
def discrete.cong₂ [DecidableEq α] (op : α → α → α) {a a' b b' : α} :
    (discrete α).rel a a' ⊓ (discrete α).rel b b' ⊢ (discrete α).rel (op a b) (op a' b') :=
  ⟨fun h => Trunc'.map₂ (fun (pa : PLift (a = a')) (pb : PLift (b = b')) =>
       ⟨by rw [pa.down, pb.down]⟩) h.1 h.2,
   fun hn => Trunc'.map (fun (p : PLift (op a b ≠ op a' b')) =>
       if hab : a = a' then
         Sum.inr (Trunc'.mk ⟨fun hbb => p.down (by rw [hab, hbb])⟩)
       else Sum.inl (Trunc'.mk ⟨hab⟩)) hn⟩

/-- Negation respects `~`. -/
class NegCong (α : Type) [AEquiv α] [Neg α] where
  neg_cong : ∀ {a a' : α}, AEquiv.rel a a' ⊢ AEquiv.rel (-a) (-a')

/-- Addition respects `~`. -/
class AddCong (α : Type) [AEquiv α] [Add α] where
  add_cong : ∀ {a a' b b' : α}, AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a + b) (a' + b')

/-- Subtraction respects `~`. -/
class SubCong (α : Type) [AEquiv α] [Sub α] where
  sub_cong : ∀ {a a' b b' : α}, AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a - b) (a' - b')

/-- Multiplication respects `~`. -/
class MulCong (α : Type) [AEquiv α] [Mul α] where
  mul_cong : ∀ {a a' b b' : α}, AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a * b) (a' * b')

/-! ## Applying and deriving morphisms -/

/-- Apply a setoid morphism like a function. -/
instance {X Y : ASetoid} : CoeFun (ASetoid.Hom X Y) (fun _ => X → Y) := ⟨ASetoid.Hom.toFun⟩

/-- Peel a named morphism off the head of an expression. -/
def homApp {Y Z : ASetoid} (m : ASetoid.Hom Y Z) {Γ : AProp} {a a' : Y}
    (h : Γ ⊢ Y.eq a a') : Γ ⊢ Z.eq (m a) (m a') := cut h (m.resp a a')

/-- A constant subterm respects `~` from any context. -/
def homConst {Γ : AProp} {Y : ASetoid} (c : Y) : Γ ⊢ Y.eq c c :=
  Entails.of_holds (Y.eqv.refl c).holds

/-- Peel a unary congruence (negation). -/
def negApp [AEquiv α] [Neg α] [NegCong α] {Γ : AProp} {a a' : α}
    (h : Γ ⊢ AEquiv.rel a a') : Γ ⊢ AEquiv.rel (-a) (-a') := cut h NegCong.neg_cong

/-- Peel a binary congruence: pair the sub-proofs with `with_intro` (cartesian,
**no contraction**), then apply the strongly-extensional congruence. -/
def addApp [AEquiv α] [Add α] [AddCong α] {Γ : AProp} {a a' b b' : α}
    (h₁ : Γ ⊢ AEquiv.rel a a') (h₂ : Γ ⊢ AEquiv.rel b b') :
    Γ ⊢ AEquiv.rel (a + b) (a' + b') := cut (with_intro h₁ h₂) AddCong.add_cong

def subApp [AEquiv α] [Sub α] [SubCong α] {Γ : AProp} {a a' b b' : α}
    (h₁ : Γ ⊢ AEquiv.rel a a') (h₂ : Γ ⊢ AEquiv.rel b b') :
    Γ ⊢ AEquiv.rel (a - b) (a' - b') := cut (with_intro h₁ h₂) SubCong.sub_cong

def mulApp [AEquiv α] [Mul α] [MulCong α] {Γ : AProp} {a a' b b' : α}
    (h₁ : Γ ⊢ AEquiv.rel a a') (h₂ : Γ ⊢ AEquiv.rel b b') :
    Γ ⊢ AEquiv.rel (a * b) (a' * b') := cut (with_intro h₁ h₂) MulCong.mul_cong

/-- Fill a morphism's `resp` for a pointfully-written `toFun`. -/
syntax "mor" : tactic
macro_rules
  | `(tactic| mor) =>
    `(tactic| first
      | exact discrete.resp _
      | (intro x x'
         repeat' first
           | exact Entails.refl _
           | apply homApp
           | apply negApp
           | apply addApp
           | apply subApp
           | apply mulApp
           | exact homConst _))

end Antithesis
