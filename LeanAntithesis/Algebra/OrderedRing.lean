import LeanAntithesis.Algebra.RingSolver
import LeanAntithesis.Sets.Ordering
import LeanAntithesis.Logic.AffineLint

/-!
# Affine ordered commutative rings

An `AOrderedRing α` is a commutative ring (`ARing`) carrying a compatible affine order
(`AOrd`): addition is monotone, scaling by a nonnegative element is monotone, equality
refines the order, and `0 ≤ 1`.  This is the structure the affine `linarith` solver
(`Algebra/LinarithSolver.lean`) runs over — a nonnegative linear combination of order
facts is *assembled* from `add_le_add`/`mul_le_mul_right`, with the ring rearrangements
discharged by `aring`.

(Combinators here legitimately take entailment/`Valid` arguments — they are the
fundamental order-arithmetic plumbing — and the file is outside the `Numbers/` layer
where the `affineHyp` linter runs.)
-/

namespace Antithesis
open scoped Antithesis

/-- `n • a` as iterated addition (`a + a + … + a`, `n` times).  Used by the `llinarith`
solver to express integer coefficients without a `NatCast` on the carrier: scaling a
resource by `n` is multiplication by `natMul n 1`, and `simp only [natMul]` reduces it to a
literal sum that `aring` understands. -/
def natMul {α : Type} [Add α] [Zero α] : ℕ → α → α
  | 0, _ => 0
  | n + 1, a => a + natMul n a

/-- A commutative ring with a compatible affine order. -/
class AOrderedRing (α : Type) extends ARing α, AOrd α where
  /-- Addition is monotone in both arguments. -/
  add_le_add : ∀ {a b c d : α}, (a ≤ₐ b) ⊗ (c ≤ₐ d) ⊢ (a + c ≤ₐ b + d)
  /-- Right multiplication by a nonnegative element is monotone. -/
  mul_le_mul_right : ∀ {a b c : α}, (0 ≤ₐ c) ⊗ (a ≤ₐ b) ⊢ (a * c ≤ₐ b * c)
  /-- `0 ≤ 1`. -/
  zero_le_one : Valid ((0 : α) ≤ₐ (1 : α))

namespace AOrderedRing
variable {α : Type} [AOrderedRing α]

/-- `a ≤ₐ b` iff `b + -a` is nonnegative (forward).  (`ARing` has `Neg`, not `Sub`, so the
generic layer uses `b + -a`.) -/
def sub_nonneg_of_le {a b : α} : (a ≤ₐ b) ⊢ (0 ≤ₐ b + -a) := by
  linear
  lintro hab
  lhave hr (AOrd.le_refl (-a))
  lcombine s hab hr add_le_add                                -- a + -a ≤ₐ b + -a
  lmap s (AOrd.le_congrL (a' := (0 : α)) (by aring))                -- 0 ≤ₐ b + -a
  lexact (Entails.refl _)

/-- `a ≤ₐ b` iff `b + -a` is nonnegative (backward). -/
def le_of_sub_nonneg {a b : α} : (0 ≤ₐ b + -a) ⊢ (a ≤ₐ b) := by
  linear
  lintro h
  lhave hr (AOrd.le_refl a)
  lcombine s h hr add_le_add                                  -- 0 + a ≤ₐ (b + -a) + a
  lmap s (AOrd.le_congr (a' := a) (b' := b) (by aring) (by aring))
  lexact (Entails.refl _)

/-- Sum of nonnegatives is nonnegative. -/
def add_nonneg {p q : α} : (0 ≤ₐ p) ⊗ (0 ≤ₐ q) ⊢ (0 ≤ₐ p + q) := by
  linear
  lintro hp hq
  lcombine s hp hq add_le_add                                 -- 0 + 0 ≤ₐ p + q
  lmap s (AOrd.le_congrL (a' := (0 : α)) (by aring))                -- 0 ≤ₐ p + q
  lexact (Entails.refl _)

/-- Scaling a nonnegative by a nonnegative stays nonnegative — both nonnegativities are
resources on the sequent. -/
def mul_nonneg {p k : α} : (0 ≤ₐ k) ⊗ (0 ≤ₐ p) ⊢ (0 ≤ₐ p * k) := by
  linear
  lintro hk hp
  lcombine s hk hp mul_le_mul_right                          -- 0 * k ≤ₐ p * k
  lmap s (AOrd.le_congrL (a' := (0 : α)) (by aring))                -- 0 ≤ₐ p * k
  lexact (Entails.refl _)

/-- `natMul n a` is nonnegative when `a` is — by induction on `n`.  The hypothesis is carried
on the sequent as the **duplicable** `!(0 ≤ₐ a)`; `ldup` reuses it at each `+` step.  This is
how induction over a reused hypothesis is done in the affine calculus: the exponential, not a
`Valid` parameter, supplies the reuse. -/
def natMul_nonneg {a : α} : (n : ℕ) → ！(0 ≤ₐ a) ⊢ (0 ≤ₐ natMul n a)
  | 0 => by simp only [natMul]; exact Entails.of_holds (AOrd.le_refl (0 : α)).holds
  | n + 1 => by
      simp only [natMul]
      linear
      ldup this ha                    -- ha : 0 ≤ₐ a ;  this : !(0 ≤ₐ a) still available
      lmap this (natMul_nonneg n)      -- this : 0 ≤ₐ natMul n a   (the induction hypothesis)
      lcombine s ha this add_nonneg
      lexact (Entails.refl _)

/-- The coefficient witness `llinarith` needs: `0 ≤ₐ natMul n 1`, a closed fact, obtained
from the general lemma by promoting `zero_le_one` to `!`. -/
def natMul_one_nonneg (n : ℕ) : Valid (0 ≤ₐ natMul n (1 : α)) :=
  cut (show Valid (！((0 : α) ≤ₐ 1)) from Valid.of_holds (zero_le_one (α := α)).holds)
    (natMul_nonneg n)

end AOrderedRing
end Antithesis
