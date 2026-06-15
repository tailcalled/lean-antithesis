import LeanAntithesis.Sets.Morphism
import LeanAntithesis.Algebra.Ring
import LeanAntithesis.Logic.AffineLint
import Mathlib.Data.Int.Notation
import Mathlib.Tactic.Ring

/-!
# The integers as an affine set

`ℤ` has decidable equality, so its antithesis structure is the discrete one:
`m ~ n` is `m = n` and the apartness `m # n` is the (decidable) `m ≠ n`.  Being
discrete, every integer operation is automatically a setoid morphism.
-/

namespace Antithesis
open scoped Antithesis

/-- The integers as an affine set: `~` is `=`, `#` is decidable `≠`. -/
instance : AEquiv ℤ := discrete ℤ

example : Valid (AEquiv.rel (2 : ℤ) 2) := AEquiv.refl _
example : Valid (AEquiv.apart (1 : ℤ) 2) := discrete.apart_of_ne (by decide)
example : Valid (AEquiv.apart (-3 : ℤ) 3) := discrete.apart_of_ne (by decide)

/-- `ℤ` is a first-class affine set. -/
example : ASetoid := .of ℤ

/-- Negation is a setoid morphism (as is every integer operation). -/
def negHom : ASetoid.Hom (.of ℤ) (.of ℤ) := ⟨Int.neg, discrete.resp Int.neg⟩

/-- Translation by a fixed integer is a morphism. -/
def addHom (k : ℤ) : ASetoid.Hom (.of ℤ) (.of ℤ) :=
  ⟨fun n : ℤ => n + k, discrete.resp fun n : ℤ => n + k⟩

/-! ## Congruence witnesses for the arithmetic operations

Being discrete, every operation respects `~`, so all the congruence instances are
populated by the `discrete.cong*` builders. -/

instance : NegCong ℤ := ⟨discrete.cong₁ fun a => -a⟩
instance : AddCong ℤ := ⟨discrete.cong₂ (· + ·)⟩
instance : SubCong ℤ := ⟨discrete.cong₂ (· - ·)⟩
instance : MulCong ℤ := ⟨discrete.cong₂ (· * ·)⟩

-- the witnesses are now available by instance resolution
example {a a' b b' : ℤ} :
    AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a + b) (a' + b') := AddCong.add_cong
example {a a' b b' : ℤ} :
    AEquiv.rel a a' ⊓ AEquiv.rel b b' ⊢ AEquiv.rel (a * b) (a' * b') := MulCong.mul_cong
example {a a' : ℤ} : AEquiv.rel a a' ⊢ AEquiv.rel (-a) (-a') := NegCong.neg_cong

/-- `ℤ` is an **affine commutative ring**: the ring axioms hold as valid discrete
equalities (`rel_of_eq` of an `Int` identity, discharged by `ring`), and the
operations are the discrete congruences.  This makes the `aring` solver available
for `ℤ`. -/
instance : ARing ℤ where
  add_assoc a b c := discrete.rel_of_eq (by ring)
  add_comm a b := discrete.rel_of_eq (by ring)
  zero_add a := discrete.rel_of_eq (by ring)
  neg_add_cancel a := discrete.rel_of_eq (by ring)
  mul_assoc a b c := discrete.rel_of_eq (by ring)
  mul_comm a b := discrete.rel_of_eq (by ring)
  one_mul a := discrete.rel_of_eq (by ring)
  left_distrib a b c := discrete.rel_of_eq (by ring)
  add_cong' := AddCong.add_cong
  mul_cong' := MulCong.mul_cong
  neg_cong' := NegCong.neg_cong

/-! ## Affine order on `ℤ`

The order, *inside the affine calculus*: `intLE a b` is an `AProp` whose affirmation
is `a ≤ b` and whose refutation (apartness side) is the strict reversal `b < a`.  The
order laws are then **sequents** — reflexivity is `Valid`, transitivity is the
multiplicative `⊗ ⊢` (composing via `cut`), monotonicity is `⊢`.  Only the atomic
`Int` facts are discharged in plain Lean (`Int` order is axiom-pure); all composition
is in the calculus.  `Rationals.lean` builds the rational order on top of these. -/

/-- Affine order on `ℤ`: affirmation `a ≤ b`, refutation the strict `b < a`. -/
def intLE (a b : ℤ) : AProp.{0} :=
  AProp.ofTypes (PLift (a ≤ b)) (PLift (b < a)) fun p q => absurd p.down (Int.not_le.mpr q.down)

/-- Strict affine order on `ℤ`: affirmation `a < b`, refutation `b ≤ a`.  (Carries
positivity facts inside the calculus, e.g. `intLT 0 c` is "`c` is positive".) -/
def intLT (a b : ℤ) : AProp.{0} :=
  AProp.ofTypes (PLift (a < b)) (PLift (b ≤ a)) fun p q => absurd p.down (Int.not_lt.mpr q.down)

/-- Positivity as a calculus fact. -/
def intLE.nonneg {c : ℤ} (h : 0 ≤ c) : Valid (intLE 0 c) := Valid.of_holds (Trunc'.mk ⟨h⟩)
/-- Strict positivity as a calculus fact. -/
def intLT.pos {c : ℤ} (h : 0 < c) : Valid (intLT 0 c) := Valid.of_holds (Trunc'.mk ⟨h⟩)

namespace intLE
variable {a b c : ℤ}

/-- Reflexivity. -/
def refl (a : ℤ) : Valid (intLE a a) := Valid.of_holds (Trunc'.mk ⟨Int.le_refl a⟩)

/-- Transitivity — multiplicative, so it composes via `cut`. -/
def trans : intLE a b ⊗ intLE b c ⊢ intLE a c :=
  AProp.ofTypes_tensor (fun p q => ⟨Int.le_trans p.down q.down⟩)
    (fun p r => ⟨Int.lt_of_lt_of_le r.down p.down⟩)
    (fun q r => ⟨Int.lt_of_le_of_lt q.down r.down⟩)

/-- Translation is monotone. -/
def addRight (c : ℤ) : intLE a b ⊢ intLE (a + c) (b + c) :=
  AProp.ofTypes_mono (fun p => ⟨Int.add_le_add_right p.down c⟩)
    (fun q => ⟨Int.lt_of_add_lt_add_right q.down⟩)

/-- Scaling: the nonnegativity of the factor is a **hypothesis in the sequent**
(`intLE 0 c`), so it composes with conditionally-established positivity. -/
def mulRight : intLE 0 c ⊗ intLE a b ⊢ intLE (a * c) (b * c) :=
  AProp.ofTypes_tensor (fun hc hab => ⟨Int.mul_le_mul_of_nonneg_right hab.down hc.down⟩)
    (fun hc r => ⟨Int.lt_of_mul_lt_mul_right r.down hc.down⟩)
    (fun hab r => ⟨Int.not_le.mp fun hc =>
      absurd (Int.mul_le_mul_of_nonneg_right hab.down hc) (Int.not_le.mpr r.down)⟩)

/-- Cancelling a factor whose **positivity is a sequent hypothesis** (`intLT 0 c`). -/
def cancelMul : intLT 0 c ⊗ intLE (a * c) (b * c) ⊢ intLE a b :=
  AProp.ofTypes_tensor (fun hc hm => ⟨Int.le_of_mul_le_mul_right hm.down hc.down⟩)
    (fun hc r => ⟨Int.mul_lt_mul_of_pos_right r.down hc.down⟩)
    (fun hm r => ⟨Int.not_lt.mp fun hc =>
      absurd (Int.mul_lt_mul_of_pos_right r.down hc) (Int.not_lt.mpr hm.down)⟩)

/-- Rewrite the endpoints along integer equalities (transport the relation). -/
def ofEq {a b a' b' : ℤ} (ha : a = a') (hb : b = b') : intLE a b ⊢ intLE a' b' := by
  rw [ha, hb]; exact Entails.refl _

/-- Transport the **left** endpoint along an affine equality carried *on the sequent*:
with `a ≈ a'` as a hypothesis, rewrite `intLE a b` to `intLE a' b`.  (`aring` supplies the
`a ≈ a'` resource.)  The equality lives in the antecedent, not as a `Valid` parameter. -/
def congrL {a a' b : ℤ} : AEquiv.rel a a' ⊗ intLE a b ⊢ intLE a' b :=
  AProp.ofTypes_tensor
    (fun ha hab => ⟨by have := ha.down; have := hab.down; omega⟩)
    (fun ha r => ⟨by have := ha.down; have := r.down; omega⟩)
    (fun hab r => ⟨by have := hab.down; have := r.down; omega⟩)

/-- Transport the **right** endpoint along an affine equality carried on the sequent. -/
def congrR {a b b' : ℤ} : AEquiv.rel b b' ⊗ intLE a b ⊢ intLE a b' :=
  AProp.ofTypes_tensor
    (fun hb hab => ⟨by have := hb.down; have := hab.down; omega⟩)
    (fun hb r => ⟨by have := hb.down; have := r.down; omega⟩)
    (fun hab r => ⟨by have := hab.down; have := r.down; omega⟩)

end intLE
end Antithesis
