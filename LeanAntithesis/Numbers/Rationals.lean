import LeanAntithesis.Numbers.Integers
import Mathlib.Algebra.Order.Ring.Abs
import LeanAntithesis.Sets.AffineRw
import LeanAntithesis.Logic.LinearTactic
import LeanAntithesis.Logic.AffineLint
import LeanAntithesis.Algebra.RingSolver
import LeanAntithesis.Algebra.OrderedRing

/-!
# Rationals, inside the affine calculus

A rational is a **transparent fraction** `Frac` (numerator over a positive
denominator, not reduced).  Its order lives *in the antithesis calculus*: `aLE a b`
is an `AProp` whose affirmation is `a ≤ b` and whose refutation (apartness side) is
the strict reversal `b < a`.  The order laws are **sequents** built from the
calculus — reflexivity is `Valid`, transitivity is the multiplicative `⊗ ⊢`
(composing via `cut`).

The whole development reduces to the affine order/equality on `ℤ`, and **`Integers.lean` owns
all the atoms** — `intLE.*` (order), `discrete.*` (equality), `intLE.cancelMulRight`,
`intLE.abs_add`, and the affine `|·|` facts `intAbsMulPos`/`intAbsNeg` (`Valid (… ≈ₐ …)`).
Every rational lemma here is *pure composition*: calculus combinators (`cut`, `tensor_mono`,
`intLE.mulRight`/`cancelMul`/`trans`, `intLE.congrL`/`congrR`, `intLE.abs_add`,
`discrete.cong₁`, `addApp`, `relSymm`) plus the affine ring solver `aring` (on ℤ) for
rearrangements and the transparent `Frac`→ℤ projection `rfl`s as the bridge.  The only
`Frac`-level atoms are the structural denominator-positivity facts (`zero_le_den`/`zero_lt_den`,
reflecting `den_pos`) and `le_of_forall_pos` (the Archimedean principle — decidability +
fraction witness).  All `Classical`-free, so the rationals are.
-/

namespace Antithesis
open scoped Antithesis

/-- A transparent rational: numerator over a positive denominator, **not** reduced. -/
structure Frac where
  /-- Numerator. -/
  num : Int
  /-- Denominator. -/
  den : Int
  /-- The denominator is positive. -/
  den_pos : 0 < den

namespace Frac

/-! ## Arithmetic — transparent, so it reduces to `Int` -/

/-- Addition (common denominator `a.den * b.den`). -/
protected def add (a b : Frac) : Frac :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩
/-- Negation. -/
protected def neg (a : Frac) : Frac := ⟨-a.num, a.den, a.den_pos⟩
/-- Subtraction. -/
protected def sub (a b : Frac) : Frac := a.add b.neg
/-- Absolute value. -/
protected def abs (a : Frac) : Frac := ⟨|a.num|, a.den, a.den_pos⟩

/-- Multiplication (numerators and denominators multiply). -/
protected def mul (a b : Frac) : Frac :=
  ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

instance : Add Frac := ⟨Frac.add⟩
instance : Neg Frac := ⟨Frac.neg⟩
instance : Sub Frac := ⟨Frac.sub⟩
instance : Mul Frac := ⟨Frac.mul⟩
instance : Zero Frac := ⟨0, 1, by omega⟩
instance : One Frac := ⟨1, 1, by omega⟩

/-! ### Projection lemmas — the operations are transparent, so these are `rfl`. -/

@[simp] theorem add_num (a b : Frac) : (a + b).num = a.num * b.den + b.num * a.den := rfl
@[simp] theorem add_den (a b : Frac) : (a + b).den = a.den * b.den := rfl
@[simp] theorem neg_num (a : Frac) : (-a).num = -a.num := rfl
@[simp] theorem neg_den (a : Frac) : (-a).den = a.den := rfl
@[simp] theorem mul_num (a b : Frac) : (a * b).num = a.num * b.num := rfl
@[simp] theorem mul_den (a b : Frac) : (a * b).den = a.den * b.den := rfl
@[simp] theorem zero_num : (0 : Frac).num = 0 := rfl
@[simp] theorem zero_den : (0 : Frac).den = 1 := rfl
@[simp] theorem one_num : (1 : Frac).num = 1 := rfl
@[simp] theorem one_den : (1 : Frac).den = 1 := rfl

/-! ### Denominator positivity — the `Frac`-structural atoms (affine reflection of `den_pos`)

These are the only `Frac`-level facts introduced by `Valid.of_holds`.  They are **specific**
— they can introduce *only* a denominator's positivity, never an arbitrary `0 ≤ c` (so there
is nothing to misuse in composition) — and they supply the sequent-side positivity that the
order combinators `intLE.mulRight`/`cancelMul` consume. -/

/-- A denominator is nonnegative. -/
def zero_le_den (a : Frac) : Valid ((0 : ℤ) ≤ₐ a.den) := Valid.of_holds (Trunc'.mk ⟨a.den_pos.le⟩)

/-- A denominator is strictly positive. -/
def zero_lt_den (a : Frac) : Valid ((0 : ℤ) <ₐ a.den) := Valid.of_holds (Trunc'.mk ⟨a.den_pos⟩)

/-- A **product** of denominators is nonnegative — *derived* in the calculus from the two
single-denominator atoms (scale `0 ≤ₐ a.den` by `b.den`, then drop `0 · b.den` to `0`). -/
def zero_le_den_mul (a b : Frac) : Valid ((0 : ℤ) ≤ₐ a.den * b.den) :=
  cut (cut (cut unit_tensor (tensor_mono (zero_le_den b) (zero_le_den a))) intLE.mulRight)
    (AOrd.le_congrL (show Valid ((0 : ℤ) * b.den ≈ₐ 0) by aring))

/-! ## Order, in the affine calculus

`aLE a b` reduces the rational order to the affine integer order `intLE` on the
cross-products `a.num * b.den` and `b.num * a.den`.  Its refutation is the strict
reversal, so apartness of rationals comes for free as `(aLE a b)ᗮ`. -/

/-- Affine order on rationals (affirmation `a ≤ b`, refutation `b < a`). -/
def aLE (a b : Frac) : AProp.{0} := intLE (a.num * b.den) (b.num * a.den)

/-- Reflexivity. -/
def aLE.refl (a : Frac) : Valid (aLE a a) := intLE.refl _

/-- Transitivity, **in the calculus**: scale each side by the other denominator
(`intLE.mulRight`, with the denominator-positivity atom `zero_le_den` supplied on the
sequent), align/transport the cross-products along affine ℤ equalities (`intLE.congrR`/
`congrL`, the `≈`-facts supplied by `aring`), chain with `intLE.trans`, and cancel the common
positive factor (`intLE.cancelMul`, fed `zero_lt_den`).  Every side-condition is a sequent
resource; no combinator takes a positivity *parameter*. -/
def aLE.trans {a b c : Frac} : aLE a b ⊗ aLE b c ⊢ aLE a c := by
  linear
  lintro hab hbc
  -- scale: hab by c.den, hbc by a.den (denominator positivity on the sequent)
  lhave pc (zero_le_den c)
  lcombine sab pc hab intLE.mulRight
  lhave pa (zero_le_den a)
  lcombine sbc pa hbc intLE.mulRight
  -- align the shared middle term, then transitivity
  lhave em (show Valid (b.num * a.den * c.den ≈ₐ b.num * c.den * a.den) by aring)
  lcombine sab' em sab intLE.congrR
  lcombine t sab' sbc intLE.trans
  -- refactor both endpoints into `· * b.den` form, then cancel `b.den`
  lhave el (show Valid (a.num * b.den * c.den ≈ₐ a.num * c.den * b.den) by aring)
  lcombine t1 el t intLE.congrL
  lhave er (show Valid (c.num * b.den * a.den ≈ₐ c.num * a.den * b.den) by aring)
  lcombine t2 er t1 intLE.congrR
  lhave pb (zero_lt_den b)
  lcombine r pb t2 intLE.cancelMul
  lexact (Entails.refl _)

/-- Transitivity of rational equality, **entirely on the sequent** — the equality analogue of
`aLE.trans`.  Scale each cross-product equality by the other denominator (`discrete.cong₁`),
align/chain through the shared middle (`aring` rearrangements + `AEquiv.trans`), refactor both
endpoints into `· * b.den` form, then cancel the positive `b.den` (`intLE.cancelMulRight`). -/
def crossEq_trans {a b c : Frac} :
    (a.num * b.den ≈ₐ b.num * a.den) ⊗ (b.num * c.den ≈ₐ c.num * b.den)
      ⊢ (a.num * c.den ≈ₐ c.num * a.den) := by
  linear
  lintro h1 h2
  lmap h1 (discrete.cong₁ (fun x : ℤ => x * c.den))
  lmap h2 (discrete.cong₁ (fun x : ℤ => x * a.den))
  lhave em (show Valid (b.num * a.den * c.den ≈ₐ b.num * c.den * a.den) by aring)
  lcombine h1' h1 em (AEquiv.trans ..)
  lcombine t h1' h2 (AEquiv.trans ..)
  lhave el (show Valid (a.num * c.den * b.den ≈ₐ a.num * b.den * c.den) by aring)
  lcombine t1 el t (AEquiv.trans ..)
  lhave er (show Valid (c.num * b.den * a.den ≈ₐ c.num * a.den * b.den) by aring)
  lcombine t2 t1 er (AEquiv.trans ..)
  lhave pb (zero_lt_den b)
  lcombine r pb t2 intLE.cancelMulRight
  lexact (Entails.refl _)

/-- `Frac` is an affine **order** (hence affine equivalence).  `≤ₐ` is `aLE`; equality
`≈ₐ` is resolved **directly** as equality of the integer cross-products `(a.num*b.den) ≈ₐ
(b.num*a.den)` (not `aLE`-both-ways).  Antisymmetry is then exactly the integer
antisymmetry on the cross-products, and `<ₐ`/apartness come for free as De Morgan duals. -/
instance : AOrd Frac where
  rel a b := a.num * b.den ≈ₐ b.num * a.den
  refl a := AEquiv.refl (a.num * a.den)
  symm a b := AEquiv.symm (a.num * b.den) (b.num * a.den)
  trans _ _ _ := crossEq_trans
  le := aLE
  le_refl := aLE.refl
  le_trans _ _ _ := aLE.trans
  le_antisymm a b := AOrd.le_antisymm (a.num * b.den) (b.num * a.den)
  le_of_eq {a b} := @AOrd.le_of_eq ℤ _ (a.num * b.den) (b.num * a.den)

/-! ## The commutative ring structure

`Frac` equality is the integer cross-product equality, so every ring axiom is a valid
`ℤ` ring identity — discharged by `frac_aring` (drop to ℤ via `rel_eq` + the projection
`rfl`s, then the affine solver `aring`, **not** raw `ring`).  The congruences are built from
the integer congruence (`discrete.cong₁`/`cong₂`) composed in the calculus. -/

/-- A `Frac` equality from the integer cross-product **identity** (`=`) — for the `abs` atoms,
where `aring` cannot apply. -/
def rel_of_eq {a b : Frac} (h : a.num * b.den = b.num * a.den) : Valid (a ≈ₐ b) :=
  discrete.rel_of_eq h

/-- `Frac`'s `≈ₐ` **is** the ℤ cross-product `≈ₐ` (definitionally) — the transparent
`Frac`→ℤ bridge for the equality, used by `frac_aring` to drop a `Frac` goal to ℤ. -/
theorem rel_eq (a b : Frac) :
    (a ≈ₐ b) = (a.num * b.den ≈ₐ b.num * a.den) := rfl

/-- Drop a `Frac` equality goal to its ℤ cross-product (`rel_eq`), expose the transparent
operations (projection `rfl`s), and close with the affine ring solver `aring` on ℤ.  No raw
`ring`: the ring axioms are discharged by the *same* affine solver the rest of the calculus
uses, one level down. -/
macro "frac_aring" : tactic =>
  `(tactic| (simp only [rel_eq, add_num, add_den, mul_num, mul_den, neg_num, neg_den,
    zero_num, zero_den, one_num, one_den]; aring))

/-! ### The congruences, *inside the calculus*

A `Frac` equality is a `ℤ` (discrete) equality of cross-products, so each congruence is the
**integer** congruence (`discrete.cong₁`/`discrete.cong₂` — these already handle the
apartness/refutation side once and for all) applied to the right linear/bilinear combination
of cross-products, then transported to the goal's cross-product form.  The transport is done
*on the sequent* in the proof mode (exactly the `aLE.trans` pattern): the two ring-rearrangement
equalities go in as `lhave` resources and compose through `AEquiv.trans` — no combinator takes
the equalities as parameters, and there is no hand-rolled evidence. -/

/-- Negation respects `≈`. -/
def negCong {a a' : Frac} : (a ≈ₐ a') ⊢ (-a ≈ₐ -a') := by
  linear
  lmap this (discrete.cong₁ (fun x : ℤ => -x))                 -- this : -X ≈ -Y
  lhave eL (show Valid ((-a).num * (-a').den ≈ₐ -(a.num * a'.den))
    by simp only [neg_num, neg_den]; aring)
  lhave eR (show Valid (-(a'.num * a.den) ≈ₐ (-a').num * (-a).den)
    by simp only [neg_num, neg_den]; aring)
  lcombine t₁ eL this (AEquiv.trans ..)
  lcombine t₂ t₁ eR (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- Addition respects `≈`: `(a+b)`'s cross-product is `(a.num·a'.den)·(b.den·b'.den)` plus
`(b.num·b'.den)·(a.den·a'.den)`, the bilinear combination of the two hypotheses. -/
def addCong {a a' b b' : Frac} : (a ≈ₐ a') ⊓ (b ≈ₐ b') ⊢ (a + b ≈ₐ a' + b') := by
  linear
  lmap this (discrete.cong₂ (fun x y : ℤ => x * (b.den * b'.den) + y * (a.den * a'.den)))
  lhave eL (show Valid ((a + b).num * (a' + b').den
      ≈ₐ a.num * a'.den * (b.den * b'.den) + b.num * b'.den * (a.den * a'.den))
    by simp only [add_num, add_den]; aring)
  lhave eR (show Valid (a'.num * a.den * (b.den * b'.den) + b'.num * b.den * (a.den * a'.den)
      ≈ₐ (a' + b').num * (a + b).den)
    by simp only [add_num, add_den]; aring)
  lcombine t₁ eL this (AEquiv.trans ..)
  lcombine t₂ t₁ eR (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- Multiplication respects `≈`: the product of the cross-products is the cross-product of
the product. -/
def mulCong {a a' b b' : Frac} : (a ≈ₐ a') ⊓ (b ≈ₐ b') ⊢ (a * b ≈ₐ a' * b') := by
  linear
  lmap this (discrete.cong₂ (fun x y : ℤ => x * y))
  lhave eL (show Valid ((a * b).num * (a' * b').den ≈ₐ a.num * a'.den * (b.num * b'.den))
    by simp only [mul_num, mul_den]; aring)
  lhave eR (show Valid (a'.num * a.den * (b'.num * b.den) ≈ₐ (a' * b').num * (a * b).den)
    by simp only [mul_num, mul_den]; aring)
  lcombine t₁ eL this (AEquiv.trans ..)
  lcombine t₂ t₁ eR (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- `Frac` is an **affine commutative ring**. -/
instance : ARing Frac where
  add_assoc a b c := by frac_aring
  add_comm a b := by frac_aring
  zero_add a := by frac_aring
  neg_add_cancel a := by frac_aring
  mul_assoc a b c := by frac_aring
  mul_comm a b := by frac_aring
  one_mul a := by frac_aring
  left_distrib a b c := by frac_aring
  add_cong' := addCong
  mul_cong' := mulCong
  neg_cong' := negCong

/-! ## Compatibility of the order with the ring structure

Each lemma scales the integer cross-products by the relevant (positive) denominators
via `intLE.mulRight`, combines them with the integer `add_le_add`, and transports the
endpoints to the goal's cross-product form **on the sequent** — every cross-product
rearrangement enters as an `≈`-resource (`lhave … by aring`) consumed by `intLE.congrL`/
`congrR` (exactly the `aLE.trans` pattern; no raw `ofEq`/`ring`).  The only Lean-level
facts are positivity of denominators. -/

/-- Addition is monotone. -/
def aLE.add_le_add {a b c d : Frac} : (a ≤ₐ b) ⊗ (c ≤ₐ d) ⊢ (a + c ≤ₐ b + d) := by
  linear
  lintro hab hcd
  lhave pcd (zero_le_den_mul c d)
  lcombine s1 pcd hab intLE.mulRight
  lhave pab (zero_le_den_mul a b)
  lcombine s2 pab hcd intLE.mulRight
  lcombine t s1 s2 (AOrderedRing.add_le_add (α := ℤ))
  lhave eL (show Valid (a.num * b.den * (c.den * d.den) + c.num * d.den * (a.den * b.den)
      ≈ₐ (a + c).num * (b + d).den) by simp only [add_num, add_den]; aring)
  lcombine t1 eL t intLE.congrL
  lhave eR (show Valid (b.num * a.den * (c.den * d.den) + d.num * c.den * (a.den * b.den)
      ≈ₐ (b + d).num * (a + c).den) by simp only [add_num, add_den]; aring)
  lcombine t2 eR t1 intLE.congrR
  lexact (Entails.refl _)

/-- Right multiplication by a nonnegative element is monotone. -/
def aLE.mul_le_mul_right {a b c : Frac} : (0 ≤ₐ c) ⊗ (a ≤ₐ b) ⊢ (a * c ≤ₐ b * c) := by
  linear
  lintro hc hab
  -- scale `hc : 0 ≤ₐ c` by `c.den` (denominator positivity on the sequent), reshape to
  -- `0 ≤ₐ c.num * c.den`
  lhave pd (zero_le_den c)
  lcombine s0 pd hc intLE.mulRight
  lhave e0L (show Valid ((0 : Frac).num * c.den * c.den ≈ₐ 0) by simp only [zero_num]; aring)
  lcombine s0a e0L s0 intLE.congrL
  lhave e0R (show Valid (c.num * (0 : Frac).den * c.den ≈ₐ c.num * c.den)
    by simp only [zero_den]; aring)
  lcombine s0b e0R s0a intLE.congrR
  -- scale `a ≤ₐ b` by the (sequent-)nonnegative `c.num * c.den`, then transport to the goal
  lcombine s1 s0b hab intLE.mulRight
  lhave eL (show Valid (a.num * b.den * (c.num * c.den) ≈ₐ (a * c).num * (b * c).den)
    by simp only [mul_num, mul_den]; aring)
  lcombine t1 eL s1 intLE.congrL
  lhave eR (show Valid (b.num * a.den * (c.num * c.den) ≈ₐ (b * c).num * (a * c).den)
    by simp only [mul_num, mul_den]; aring)
  lcombine t2 eR t1 intLE.congrR
  lexact (Entails.refl _)

/-- `Frac` is an **affine ordered commutative ring** — the carrier the `llinarith`
solver runs over, and (being a field of fractions) the one whose division will let
`llinarith` clear rational coefficients. -/
instance : AOrderedRing Frac where
  add_le_add := aLE.add_le_add
  mul_le_mul_right := aLE.mul_le_mul_right
  zero_le_one := Valid.of_holds (Trunc'.mk ⟨by decide⟩)

/-! ## Order, absolute value, and limits — the analysis layer for the reals, *in the calculus*

Built the framework way.  The **atoms** (`le_of_num`, `abs_cong`, `abs_neg`, `abs_triangle`,
`le_of_forall_pos`) each discharge one irreducible integer fact about the cross-products —
exactly as `intLE.mulRight`/`discrete.cong₁` do — and everything else is *composed* from them
in the `linear` proof mode (`lhave`/`lmap`/`lcombine` + `aring`/`asimp`).  The transparent
`Frac`↔ℤ projection equalities are the bridge the atoms reduce across; they appear only
*inside* atoms, never to prove a derived fact. -/

/-- A valid `≤ₐ` from the integer cross-product inequality — the order analogue of `rel_of_eq`,
the `Frac` order's `Valid` constructor (`a ≤ₐ b` *is* `intLE (a.num*b.den) (b.num*a.den)`). -/
def le_of_num {a b : Frac} (h : a.num * b.den ≤ b.num * a.den) : Valid (a ≤ₐ b) :=
  Valid.of_holds (Trunc'.mk ⟨h⟩)

-- The transparent `Frac`↔ℤ bridge, used only to expose the cross-products for the ℤ atoms.
theorem abs_num (a : Frac) : a.abs.num = |a.num| := rfl
theorem abs_den (a : Frac) : a.abs.den = a.den := rfl

/-- Absolute value respects equality, `(a ≈ₐ b) ⊢ (|a| ≈ₐ |b|)` — composed in the calculus:
`discrete.cong₁ |·|` on the cross-products, then refold `|x·d| ≈ₐ |x|·d` (`intAbsMulPos`). -/
@[asimp] def abs_cong {a b : Frac} : (a ≈ₐ b) ⊢ (a.abs ≈ₐ b.abs) := by
  linear
  lintro h
  lmap h (discrete.cong₁ (fun x : ℤ => |x|))
  lhave eL (relSymm (cut (zero_le_den b) (intAbsMulPos a.num)))  -- |an|·bd ≈ₐ |an·bd|
  lhave eR (cut (zero_le_den a) (intAbsMulPos b.num))            -- |bn·ad| ≈ₐ |bn|·ad
  lcombine t₁ eL h (AEquiv.trans ..)
  lcombine t₂ t₁ eR (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- `|-a| ≈ₐ |a|` — the numerator fact `intAbsNeg` (`|-an| ≈ₐ |an|`) scaled by the denominator
(`discrete.cong₁ (· * a.den)`). -/
@[asimp] def abs_neg (a : Frac) : Valid ((-a).abs ≈ₐ a.abs) :=
  cut (intAbsNeg a.num) (discrete.cong₁ (fun x : ℤ => x * a.den))

/-- `|0| ≈ₐ 0`. -/
@[asimp] def abs_zero : Valid ((0 : Frac).abs ≈ₐ 0) :=
  rel_of_eq (by simp only [abs_num, abs_den, zero_num, zero_den, _root_.abs_zero])

/-- The triangle inequality `|a + b| ≤ₐ |a| + |b|` — composed in the calculus from the atomic
ℤ triangle `intLE.abs_add`: refold the abs-products on the right (`intAbsMulPos`, via
`le_congrR`), then scale by the common positive denominator (`intLE.mulRight`). -/
def abs_triangle (a b : Frac) : Valid ((a + b).abs ≤ₐ a.abs + b.abs) :=
  -- `|an·bd + bn·ad| ≤ₐ |an|·bd + |bn|·ad` on the numerators…
  have tri : Valid (|a.num * b.den + b.num * a.den| ≤ₐ |a.num| * b.den + |b.num| * a.den) :=
    cut (intLE.abs_add (a.num * b.den) (b.num * a.den))
      (AOrd.le_congrR (addApp (cut (zero_le_den b) (intAbsMulPos a.num))
        (cut (zero_le_den a) (intAbsMulPos b.num))))
  -- …then scale both sides by the common (positive) denominator `a.den · b.den`.
  cut (cut unit_tensor (tensor_mono (zero_le_den_mul a b) tri)) intLE.mulRight

/-- `|a - b| ≈ₐ |b - a|` — composed in the calculus: rewrite `a - b ≈ₐ -(b - a)` (`aring`) under
`abs` (`abs_cong`), then `abs_neg`. -/
def abs_sub_comm (a b : Frac) : Valid ((a - b).abs ≈ₐ (b - a).abs) :=
  relTrans (cut (show Valid (a - b ≈ₐ -(b - a)) by aring) abs_cong) (abs_neg (b - a))

/-- The triangle inequality `|a - c| ≤ₐ |a - b| + |b - c|` — composed in the calculus: rewrite
`a - c ≈ₐ (a - b) + (b - c)` (`aring`) under `abs` (so the difference becomes a sum), then the
`abs_triangle` atom. -/
def abs_sub_le (a b c : Frac) : Valid ((a - c).abs ≤ₐ (a - b).abs + (b - c).abs) :=
  AOrd.leTrans
    (cut (cut (show Valid (a - c ≈ₐ (a - b) + (b - c)) by aring) abs_cong) AOrd.le_of_eq)
    (abs_triangle (a - b) (b - c))

/-- Halve a fraction (double the denominator). -/
def half (q : Frac) : Frac := ⟨q.num, 2 * q.den, by have := q.den_pos; omega⟩
theorem half_num (q : Frac) : (half q).num = q.num := rfl
theorem half_den (q : Frac) : (half q).den = 2 * q.den := rfl

/-- `q/2 + q/2 ≈ₐ q` — a normalisation rule for `asimp`. -/
@[asimp] def half_add_half (q : Frac) : Valid (half q + half q ≈ₐ q) :=
  by simp only [rel_eq, add_num, add_den, half_num, half_den]; aring

/-- A strictly-positive fraction — a precision for the reals. -/
abbrev PosFrac := {q : Frac // 0 < q.num}

/-- The precision `(a-b)/2` (positive when `b < a`), used to separate `b` from `a`. -/
private def midWitness (a b : Frac) : Frac :=
  ⟨a.num * b.den - b.num * a.den, 2 * (a.den * b.den),
   by have := Int.mul_pos a.den_pos b.den_pos; omega⟩

/-- `b + (a-b)/2 < a` (as cross-products) whenever `b < a`: the separation that powers both
directions of `le_of_forall_pos`. -/
private theorem midWitness_sep (a b : Frac) :
    a.num * (b + midWitness a b).den - (b + midWitness a b).num * a.den
      = (a.num * b.den - b.num * a.den) * (a.den * b.den) := by
  simp only [add_num, add_den, midWitness]; ring

/-- **Atom** (the Archimedean principle): if `a ≤ₐ b + η` for *every* positive `η` — supplied
as an `⨅`-resource on the sequent, not a `Valid` parameter — then `a ≤ₐ b`.  Decidability of
the ℤ cross-product order keeps it `Classical`-free. -/
def le_of_forall_pos {a b : Frac} :
    AProp.all (fun η : PosFrac => a ≤ₐ b + η.val) ⊢ (a ≤ₐ b) := by
  have hda := a.den_pos; have hdb := b.den_pos
  refine ⟨fun fpos => Trunc'.mk ⟨?_⟩, fun bneg => ?_⟩
  · -- affirmation: from the whole family, conclude `a.num*b.den ≤ b.num*a.den`
    refine if hc : a.num * b.den ≤ b.num * a.den then hc else ?_
    exfalso
    have hlt : 0 < a.num * b.den - b.num * a.den := by omega
    have hwpos : (0 : ℤ) < (midWitness a b).num := by simp only [midWitness]; omega
    -- the family at `(a-b)/2` says `a ≤ b + (a-b)/2`; but `b + (a-b)/2 < a` — contradiction
    have hle : a.num * (b + midWitness a b).den ≤ (b + midWitness a b).num * a.den :=
      (Trunc'.elimProp (fun p => p) (fpos ⟨midWitness a b, hwpos⟩)).down
    have hp : 0 < (a.num * b.den - b.num * a.den) * (a.den * b.den) :=
      Int.mul_pos hlt (Int.mul_pos hda hdb)
    have hsep := midWitness_sep a b
    omega
  · -- refutation: from `b < a`, exhibit the separating precision `(a-b)/2`
    refine Trunc'.elimProp (fun blt => ?_) bneg
    have hlt : 0 < a.num * b.den - b.num * a.den := by have := blt.down; omega
    have hwpos : (0 : ℤ) < (midWitness a b).num := by simp only [midWitness]; omega
    have hstrict : (b + midWitness a b).num * a.den < a.num * (b + midWitness a b).den := by
      have hp : 0 < (a.num * b.den - b.num * a.den) * (a.den * b.den) :=
        Int.mul_pos hlt (Int.mul_pos hda hdb)
      have hsep := midWitness_sep a b
      omega
    exact Trunc'.mk ⟨⟨midWitness a b, hwpos⟩, Trunc'.mk ⟨hstrict⟩⟩

end Frac
end Antithesis
