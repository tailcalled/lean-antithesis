import LeanAntithesis.Sets.Morphism
import LeanAntithesis.Sets.AffineRw
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

variable {R : Type}

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

/- The derived ring lemmas are proved by `arw` — directed rewriting for `≈ₐ` (the affine
analogue of `rw`): each step rewrites the left side by an axiom instance, lifting it through
the surrounding operations by congruence automatically.  No hand-written `relTrans`/`App`
chains. -/

variable (a b c : R)

/-- Left-commutativity of `+` (derived; used by the solver's reordering). -/
def add_left_comm : Valid (AEquiv.rel (a + (b + c)) (b + (a + c))) := by
  arw [relSymm (add_assoc a b c), add_comm a b, add_assoc b a c]

/-- Left-commutativity of `*`. -/
def mul_left_comm : Valid (AEquiv.rel (a * (b * c)) (b * (a * c))) := by
  arw [relSymm (mul_assoc a b c), mul_comm a b, mul_assoc b a c]

/-- `0` is also a right identity. -/
def add_zero : Valid (AEquiv.rel (a + 0) a) := by
  arw [add_comm a 0, zero_add a]

/-- `1` is also a right identity. -/
def mul_one : Valid (AEquiv.rel (a * 1) a) := by
  arw [mul_comm a 1, one_mul a]

/-- `-a` is also a right inverse. -/
def add_neg_cancel : Valid (AEquiv.rel (a + -a) 0) := by
  arw [add_comm a (-a), neg_add_cancel a]

/-- Right distributivity: commute, distribute, commute the two factors back. -/
def right_distrib : Valid (AEquiv.rel ((a + b) * c) (a * c + b * c)) := by
  arw [mul_comm (a + b) c, left_distrib c a b, mul_comm c a, mul_comm c b]

end ARing
end Antithesis
