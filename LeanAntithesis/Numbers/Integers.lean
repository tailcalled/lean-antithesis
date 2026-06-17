import LeanAntithesis.Sets.Morphism
import LeanAntithesis.Sets.Ordering
import LeanAntithesis.Algebra.Ring
import LeanAntithesis.Algebra.OrderedRing
import LeanAntithesis.Logic.AffineLint
import Mathlib.Data.Int.Notation
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Abs

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

namespace intLE
variable {a b c : ℤ}

/-! ### Bootstrap laws.  These three *build* the `AOrd ℤ` instance — i.e. they are what
`≤ₐ`/`≈ₐ` *reduce to* for `ℤ` — so they must be phrased in terms of `intLE` directly. -/

/-- Reflexivity. -/
def refl (a : ℤ) : Valid (intLE a a) := Valid.of_holds (Trunc'.mk ⟨Int.le_refl a⟩)

/-- Transitivity — multiplicative, so it composes via `cut`. -/
def trans : intLE a b ⊗ intLE b c ⊢ intLE a c :=
  AProp.ofTypes_tensor (fun p q => ⟨Int.le_trans p.down q.down⟩)
    (fun p r => ⟨Int.lt_of_lt_of_le r.down p.down⟩)
    (fun q r => ⟨Int.lt_of_le_of_lt q.down r.down⟩)

/-- Antisymmetry — pinches the order down to the (discrete) equivalence. -/
def antisymm : intLE a b ⊗ intLE b a ⊢ AEquiv.rel a b :=
  AProp.ofTypes_tensor
    (fun h1 h2 => ⟨by have := h1.down; have := h2.down; omega⟩)
    (fun h1 r => ⟨by have := h1.down; have := r.down; omega⟩)
    (fun h2 r => ⟨by have := h2.down; have := r.down; omega⟩)

end intLE

/-- `ℤ` is an affine **order**: `≤ₐ` is `intLE`.  Defined here, right after the bootstrap
laws, so that the order lemmas below can be stated with the `≤ₐ`/`<ₐ`/`≈ₐ` notation. -/
instance : AOrd ℤ where
  le := intLE
  le_refl := intLE.refl
  le_trans _ _ _ := intLE.trans
  le_antisymm _ _ := intLE.antisymm
  le_of_eq :=
    AProp.ofTypes_mono (fun h => ⟨by have := h.down; omega⟩) (fun h => ⟨by have := h.down; omega⟩)

namespace intLE
variable {a b c : ℤ}

/-- Translation is monotone. -/
def addRight (c : ℤ) : (a ≤ₐ b) ⊢ (a + c ≤ₐ b + c) :=
  AProp.ofTypes_mono (fun p => ⟨Int.add_le_add_right p.down c⟩)
    (fun q => ⟨Int.lt_of_add_lt_add_right q.down⟩)

/-- Scaling: the nonnegativity of the factor is a **hypothesis in the sequent**
(`0 ≤ₐ c`), so it composes with conditionally-established positivity. -/
def mulRight : (0 ≤ₐ c) ⊗ (a ≤ₐ b) ⊢ (a * c ≤ₐ b * c) :=
  AProp.ofTypes_tensor (fun hc hab => ⟨Int.mul_le_mul_of_nonneg_right hab.down hc.down⟩)
    (fun hc r => ⟨Int.lt_of_mul_lt_mul_right r.down hc.down⟩)
    (fun hab r => ⟨Int.not_le.mp fun hc =>
      absurd (Int.mul_le_mul_of_nonneg_right hab.down hc) (Int.not_le.mpr r.down)⟩)

/-- Workhorse cancellation, with positivity as `1 ≤ c` (⟺ `0 < c` on `ℤ`). -/
def cancelMul₁ : (1 ≤ₐ c) ⊗ (a * c ≤ₐ b * c) ⊢ (a ≤ₐ b) :=
  AProp.ofTypes_tensor
    (fun hc hm => ⟨Int.le_of_mul_le_mul_right hm.down (by have := hc.down; omega)⟩)
    (fun hc r => ⟨Int.mul_lt_mul_of_pos_right r.down (by have := hc.down; omega)⟩)
    (fun hm r => ⟨Int.not_le.mp fun h1 =>
      absurd (Int.mul_lt_mul_of_pos_right r.down (show (0:ℤ) < c by omega))
        (Int.not_lt.mpr hm.down)⟩)

/-- The derived strict positivity `0 <ₐ c` entails `1 ≤ c` on `ℤ`. -/
def one_le_of_pos : (0 <ₐ c) ⊢ (1 ≤ₐ c) :=
  ⟨Trunc'.map fun p => ⟨by have := p.down; omega⟩,
   Trunc'.map fun p => ⟨by have := p.down; omega⟩⟩

/-- Cancelling a **strictly positive** factor — positivity supplied on the sequent as the
derived strict order `0 <ₐ c`. -/
def cancelMul : (0 <ₐ c) ⊗ (a * c ≤ₐ b * c) ⊢ (a ≤ₐ b) :=
  cut (tensor_mono one_le_of_pos (Entails.refl _)) cancelMul₁

/-- Transport the **left** endpoint along an affine equality carried *on the sequent*:
with `a ≈ₐ a'` as a hypothesis, rewrite `a ≤ₐ b` to `a' ≤ₐ b` (`aring` supplies the
`a ≈ₐ a'` resource).  The equality lives in the antecedent, not as a `Valid` parameter. -/
def congrL {a a' b : ℤ} : (a ≈ₐ a') ⊗ (a ≤ₐ b) ⊢ (a' ≤ₐ b) :=
  AProp.ofTypes_tensor
    (fun ha hab => ⟨by have := ha.down; have := hab.down; omega⟩)
    (fun ha r => ⟨by have := ha.down; have := r.down; omega⟩)
    (fun hab r => ⟨by have := hab.down; have := r.down; omega⟩)

/-- Transport the **right** endpoint along an affine equality carried on the sequent. -/
def congrR {a b b' : ℤ} : (b ≈ₐ b') ⊗ (a ≤ₐ b) ⊢ (a ≤ₐ b') :=
  AProp.ofTypes_tensor
    (fun hb hab => ⟨by have := hb.down; have := hab.down; omega⟩)
    (fun hb r => ⟨by have := hb.down; have := r.down; omega⟩)
    (fun hab r => ⟨by have := hab.down; have := r.down; omega⟩)

/-- Equality cancellation with positivity as `1 ≤ c` (`= ofTypes`, so `ofTypes_tensor` applies
directly — `0 <ₐ c` is a `perp` and would not). -/
def cancelMulRight₁ {a b c : ℤ} : (1 ≤ₐ c) ⊗ (a * c ≈ₐ b * c) ⊢ (a ≈ₐ b) :=
  AProp.ofTypes_tensor
    (fun hc hm => ⟨mul_right_cancel₀ (by have := hc.down; omega) hm.down⟩)
    (fun hc r => ⟨fun e => r.down (mul_right_cancel₀ (by have := hc.down; omega) e)⟩)
    (fun hm r => ⟨Int.not_le.mp fun h1 => r.down (mul_right_cancel₀ (by omega) hm.down)⟩)

/-- Cancel a **strictly positive** factor from an integer equality — positivity **on the
sequent** `(0 <ₐ c) ⊗ (a·c ≈ₐ b·c) ⊢ (a ≈ₐ b)`, the equality analogue of `cancelMul`. -/
def cancelMulRight {a b c : ℤ} : (0 <ₐ c) ⊗ (a * c ≈ₐ b * c) ⊢ (a ≈ₐ b) :=
  cut (tensor_mono one_le_of_pos (Entails.refl _)) cancelMulRight₁

/-- The **triangle inequality** `|x + y| ≤ₐ |x| + |y|` — the one primitive fact about `|·|`. -/
def abs_add (x y : ℤ) : Valid (|x + y| ≤ₐ |x| + |y|) :=
  Valid.of_holds (Trunc'.mk ⟨abs_add_le x y⟩)

end intLE

/-! ### Absolute value on `ℤ` — the few atomic facts the rational `|·|` reduces to.

`|·|` is not a ring operation, so its primitive facts are **affine atoms** (`Valid (… ≈ₐ …)`),
their `ℤ` content discharged in plain Lean inside the atom (`natAbs` — `Classical`-free, unlike
Mathlib's generic `abs_mul` — and `abs_of_pos`/`abs_neg`).  `Rationals` *composes* them
(`AEquiv.trans`/`discrete.cong₁`/`addApp`); it never rewrites with a raw `ℤ` `|·|`-equation. -/

/-- `|a·b| = |a|·|b|` on `ℤ`, via `natAbs` — the `ℤ` content behind `intAbsMulPos`. -/
private theorem natAbs_mul (a b : ℤ) : |a * b| = |a| * |b| := by
  rw [Int.abs_eq_natAbs, Int.natAbs_mul, Nat.cast_mul, Int.abs_eq_natAbs a, Int.abs_eq_natAbs b]

/-- `|x·d| ≈ₐ |x|·d`, with nonnegativity of `d` **on the sequent** `(0 ≤ₐ d) ⊢ (|x·d| ≈ₐ |x|·d)`
— refold a (nonnegative) denominator out of `|·|`. -/
def intAbsMulPos (x : ℤ) {d : ℤ} : (0 ≤ₐ d) ⊢ (|x * d| ≈ₐ |x| * d) :=
  AProp.ofTypes_mono (fun hd => ⟨by rw [natAbs_mul, abs_of_nonneg hd.down]⟩)
    (fun hne => ⟨Int.not_le.mp fun hd => hne.down (by rw [natAbs_mul, abs_of_nonneg hd])⟩)

/-- `|-x| ≈ₐ |x|`. -/
def intAbsNeg (x : ℤ) : Valid (|-x| ≈ₐ |x|) := discrete.rel_of_eq (abs_neg x)

/-- `ℤ` is an affine **ordered ring**: addition and nonnegative scaling are monotone. -/
instance : AOrderedRing ℤ where
  add_le_add :=
    AProp.ofTypes_tensor
      (fun h1 h2 => ⟨by have := h1.down; have := h2.down; omega⟩)
      (fun h1 r => ⟨by have := h1.down; have := r.down; omega⟩)
      (fun h2 r => ⟨by have := h2.down; have := r.down; omega⟩)
  mul_le_mul_right := intLE.mulRight
  zero_le_one := Valid.of_holds (Trunc'.mk ⟨by omega⟩)

end Antithesis
