import LeanAntithesis.Sets.Morphism
import LeanAntithesis.Logic.LinearTactic
import LeanAntithesis.Logic.AffineLint

/-!
# Affine commutative rings

An `ARing R` is a commutative ring *in the antithesis calculus*: a type with affine
equality (`AEquiv`), the ring operations as **strongly-extensional morphisms** (the
`AddCong`/`MulCong`/`NegCong` congruences), and the ring axioms stated as affine
equalities `Valid (rel … …)`.  Because equality is `≈` (and apartness its free dual),
every consequence proved here is automatically an apartness fact too.

The axioms are a minimal generating set; the rest of the usual ring lemmas are
*derived* (below) by chaining them with `relTrans`/`relSymm` and lifting through the
congruences with `addApp`/`mulApp`/`negApp`.  This is the groundwork an affine `ring`
solver normalises against.
-/

namespace Antithesis
open scoped Antithesis

/-! ## Generic `AEquiv` reasoning helpers (compose `Valid` equalities).

These compose/flip **closed** equality theorems at the term level — their sequent-style
equivalents are the class fields `AEquiv.trans`/`AEquiv.symm` (used directly in proof mode).
They legitimately take `Valid` arguments (there is no non-trivial sequent to host a *closed*
theorem on), and they are needed in term-mode/reflective definitions where the proof mode is
unavailable, so the `affineHyp` linter is switched off for them. -/

variable {R : Type}

set_option linter.affineHyp false in
/-- Compose two valid equalities (multiplicative transitivity at `⊤`). -/
def relTrans [AEquiv R] {x y z : R}
    (h₁ : Valid (AEquiv.rel x y)) (h₂ : Valid (AEquiv.rel y z)) : Valid (AEquiv.rel x z) :=
  cut (cut unit_tensor (tensor_mono h₁ h₂)) (AEquiv.trans x y z)

set_option linter.affineHyp false in
/-- Flip a valid equality. -/
def relSymm [AEquiv R] {x y : R}
    (h : Valid (AEquiv.rel x y)) : Valid (AEquiv.rel y x) :=
  cut h (AEquiv.symm x y)

/-! ## The affine commutative ring -/

/-- A commutative ring whose equality is affine (`AEquiv`).  Operations are
congruences; axioms are valid affine equalities. -/
class ARing (R : Type) extends AEquiv R, Zero R, One R, Add R, Neg R, Mul R where
  /-- `+` is associative. -/
  add_assoc : ∀ a b c : R, Valid (AEquiv.rel (a + b + c) (a + (b + c)))
  /-- `+` is commutative. -/
  add_comm : ∀ a b : R, Valid (AEquiv.rel (a + b) (b + a))
  /-- `0` is a left identity. -/
  zero_add : ∀ a : R, Valid (AEquiv.rel (0 + a) a)
  /-- `-a` is a left inverse. -/
  neg_add_cancel : ∀ a : R, Valid (AEquiv.rel (-a + a) 0)
  /-- `*` is associative. -/
  mul_assoc : ∀ a b c : R, Valid (AEquiv.rel (a * b * c) (a * (b * c)))
  /-- `*` is commutative. -/
  mul_comm : ∀ a b : R, Valid (AEquiv.rel (a * b) (b * a))
  /-- `1` is a left identity. -/
  one_mul : ∀ a : R, Valid (AEquiv.rel (1 * a) a)
  /-- `*` distributes over `+` on the left. -/
  left_distrib : ∀ a b c : R, Valid (AEquiv.rel (a * (b + c)) (a * b + a * c))
  /-- `+` respects `≈` (strong extensionality). -/
  add_cong' : ∀ {a a' b b' : R}, AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a + b) (a' + b')
  /-- `*` respects `≈`. -/
  mul_cong' : ∀ {a a' b b' : R}, AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a * b) (a' * b')
  /-- `-` respects `≈`. -/
  neg_cong' : ∀ {a a' : R}, AEquiv.rel a a' ⊢ AEquiv.rel (-a) (-a')

namespace ARing
variable [ARing R]

instance : AddCong R := ⟨ARing.add_cong'⟩
instance : MulCong R := ⟨ARing.mul_cong'⟩
instance : NegCong R := ⟨ARing.neg_cong'⟩

/- The `*CongV` helpers lift **closed** equality theorems through the ring operations; the
sequent-style congruences are the class fields `add_cong'`/`mul_cong'`/`neg_cong'` (and the
proof-mode `lcut … ; lwith` they are built from).  As closed-theorem composers they take
`Valid` arguments, so the `affineHyp` linter is off for them. -/
section
set_option linter.affineHyp false

/-- Lift two valid equalities through `+` (the `+`-congruence), proved natively in
the proof mode: cut the congruence onto the goal, then `lwith` splits the resulting
`⊓`-goal into the two equality obligations. -/
def addCongV {a a' b b' : R} (h₁ : Valid (AEquiv.rel a a')) (h₂ : Valid (AEquiv.rel b b')) :
    Valid (AEquiv.rel (a + b) (a' + b')) := by
  linear
  lcut AddCong.add_cong
  lwith
  · lexact h₁
  · lexact h₂

/-- Lift two valid equalities through `*`. -/
def mulCongV {a a' b b' : R} (h₁ : Valid (AEquiv.rel a a')) (h₂ : Valid (AEquiv.rel b b')) :
    Valid (AEquiv.rel (a * b) (a' * b')) := by
  linear
  lcut MulCong.mul_cong
  lwith
  · lexact h₁
  · lexact h₂

/-- Lift a valid equality through negation. -/
def negCongV {a a' : R} (h : Valid (AEquiv.rel a a')) : Valid (AEquiv.rel (-a) (-a')) := by
  linear; lcut NegCong.neg_cong; lexact h

end

variable (a b c : R)

/-- Left-commutativity of `+` (derived; used by the solver's reordering). -/
def add_left_comm : Valid (AEquiv.rel (a + (b + c)) (b + (a + c))) := by
  linear; lweaken this
  lhave h₁ (relSymm (add_assoc a b c))               -- a+(b+c) ≈ (a+b)+c
  lhave h₂ (addCongV (add_comm a b) (AEquiv.refl c))  -- (a+b)+c ≈ (b+a)+c
  lhave h₃ (add_assoc b a c)                          -- (b+a)+c ≈ b+(a+c)
  lcombine r₁ h₁ h₂ (AEquiv.trans ..)
  lcombine r r₁ h₃ (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- Left-commutativity of `*`. -/
def mul_left_comm : Valid (AEquiv.rel (a * (b * c)) (b * (a * c))) := by
  linear; lweaken this
  lhave h₁ (relSymm (mul_assoc a b c))
  lhave h₂ (mulCongV (mul_comm a b) (AEquiv.refl c))
  lhave h₃ (mul_assoc b a c)
  lcombine r₁ h₁ h₂ (AEquiv.trans ..)
  lcombine r r₁ h₃ (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- `0` is also a right identity (commute, then `zero_add`).  Proved in the `linear`
proof mode: the two equalities go in as resources and compose through `AEquiv.trans`. -/
def add_zero : Valid (AEquiv.rel (a + 0) a) := by
  linear; lweaken this
  lhave h₁ (add_comm a 0)            -- a + 0 ≈ 0 + a
  lhave h₂ (zero_add a)              -- 0 + a ≈ a
  lcombine r h₁ h₂ (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- `1` is also a right identity. -/
def mul_one : Valid (AEquiv.rel (a * 1) a) := by
  linear; lweaken this
  lhave h₁ (mul_comm a 1)            -- a * 1 ≈ 1 * a
  lhave h₂ (one_mul a)               -- 1 * a ≈ a
  lcombine r h₁ h₂ (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- `-a` is also a right inverse. -/
def add_neg_cancel : Valid (AEquiv.rel (a + -a) 0) := by
  linear; lweaken this
  lhave h₁ (add_comm a (-a))         -- a + -a ≈ -a + a
  lhave h₂ (neg_add_cancel a)        -- -a + a ≈ 0
  lcombine r h₁ h₂ (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- Right distributivity: commute the product, distribute, commute back.  Every step
lives in the proof mode — the congruence step uses the proof-mode `addCongV` (no
`addApp` combinator), and the chain is composed through `AEquiv.trans`. -/
def right_distrib : Valid (AEquiv.rel ((a + b) * c) (a * c + b * c)) := by
  linear; lweaken this
  lhave h₁ (mul_comm (a + b) c)                     -- (a+b)*c ≈ c*(a+b)
  lhave h₂ (left_distrib c a b)                     -- c*(a+b) ≈ c*a + c*b
  lhave h₃ (addCongV (mul_comm c a) (mul_comm c b)) -- c*a + c*b ≈ a*c + b*c
  lcombine r₁ h₁ h₂ (AEquiv.trans ..)               -- (a+b)*c ≈ c*a + c*b
  lcombine r r₁ h₃ (AEquiv.trans ..)                -- (a+b)*c ≈ a*c + b*c
  lexact (Entails.refl _)

end ARing
end Antithesis
