import LeanAntithesis.Numbers.Rationals
import LeanAntithesis.Logic.AffineLint

/-!
# The reals as an affine set (constructive, `Classical`-free)

A constructive real is its own **approximation function** `approx : PosFrac → Frac` with a
regularity bound `|approx ε - approx δ| ≤ₐ ε + δ`.  Equality is **undecidable** and apartness
is **primitive**: both live in one `AProp`, the universal of `≤ₐ`-atoms over a pair of
precisions, so `x # y` (the refutation side) is "some rational lies strictly between `x`
and `y`".

Everything runs over `Frac` (the affine ordered ring) and its affine order `≤ₐ`, and every
proof is composed in the calculus from the `Frac` atoms (`abs_cong`, `abs_triangle`,
`abs_sub_comm`, `le_of_forall_pos`, …) — so the development is `Classical`-free, unlike a
`Mathlib`-ℚ version whose order pulls `Classical.choice` into proof terms.
-/

namespace Antithesis
open scoped Antithesis

/-- A precision: a strictly-positive fraction. -/
abbrev PosFrac := Frac.PosFrac

/-- A constructive real: a regular rational approximation function. -/
structure Real where
  /-- `approx ε` approximates the real to precision `ε`. -/
  approx : PosFrac → Frac
  /-- Regularity: the approximations cohere to the sum of their precisions. -/
  reg : ∀ ε δ : PosFrac, Valid ((approx ε - approx δ).abs ≤ₐ ε.val + δ.val)

namespace Real

/-- Equality **and** apartness in one `AProp`: the universal of the regularity `≤ₐ`-atoms over
a pair of precisions.  `(rel x y)⁺` is `∀ ε δ, |x ε - y δ| ≤ ε + δ` (the approximations agree);
`(rel x y)⁻` is `∃ ε δ, ε + δ < |x ε - y δ|` (a rational strictly separates them). -/
def rel (x y : Real) : AProp.{0} :=
  AProp.all fun p : PosFrac × PosFrac =>
    (x.approx p.1 - y.approx p.2).abs ≤ₐ (p.1.val + p.2.val)

/-- `ℝ` is an affine set with **primitive apartness** — every law is composed in the calculus
from the `Frac` atoms. -/
instance : AEquiv Real where
  rel := rel
  -- reflexivity is exactly regularity, at each precision pair
  refl x := all_intro fun p => x.reg p.1 p.2
  -- symmetry: read off the swapped precisions, then `|x δ - y ε| ≈ |y ε - x δ|` and `δ+ε ≈ ε+δ`
  symm x y := all_intro fun p =>
    cut (all_elim (p.2, p.1)) (AOrd.le_congr (Frac.abs_sub_comm _ _) (by aring))
  -- transitivity: for each precision pair and every slack `η`, route through `y` at `η/2` —
  -- triangle inequality + adding the two bounds gives `≤ (ε+δ) + (η/2 + η/2) = (ε+δ) + η`;
  -- `le_of_forall_pos` then removes the slack.
  trans x y z := all_intro fun p =>
    cut
      (all_intro fun η : PosFrac =>
        let γ : PosFrac := ⟨Frac.half η.val, by rw [Frac.half_num]; exact η.2⟩
        have hγ : Valid ((p.1.val + γ.val) + (γ.val + p.2.val)
            ≈ₐ (p.1.val + p.2.val) + (γ.val + γ.val)) := by aring
        have hη : Valid ((p.1.val + p.2.val) + (γ.val + γ.val)
            ≈ₐ (p.1.val + p.2.val) + η.val) := by arw [Frac.half_add_half η.val]
        cut
          (cut
            (cut (tensor_mono (all_elim (p.1, γ)) (all_elim (γ, p.2))) Frac.aLE.add_le_add)
            (AOrd.le_transL (Frac.abs_sub_le (x.approx p.1) (y.approx γ) (z.approx p.2))))
          (AOrd.le_congrR (relTrans hγ hη)))
      Frac.le_of_forall_pos

/-- `ℝ` is a first-class affine set. -/
example : ASetoid := .of Real

/-- The constant real `q` — regularity is `|q - q| ≈ₐ 0 ≤ₐ ε + δ`. -/
def const (q : Frac) : Real where
  approx _ := q
  reg ε δ :=
    have e0 : Valid ((q - q).abs ≈ₐ 0) :=
      relTrans (cut (show Valid (q - q ≈ₐ (0 : Frac)) by aring) Frac.abs_cong) Frac.abs_zero
    have h0 : Valid ((0 : Frac) ≤ₐ ε.val + δ.val) :=
      Frac.le_of_num (by
        simp only [Frac.zero_num, Frac.zero_den, Frac.add_num]
        have := Int.mul_pos ε.2 δ.val.den_pos
        have := Int.mul_pos δ.2 ε.val.den_pos
        omega)
    cut h0 (AOrd.le_congrL (relSymm e0))

/-- The constant reals are reflexively equal. -/
example : Valid (const 0 ≈ₐ const 0) := AEquiv.refl _

/-- `0` and `1` are **apart** — a rational lies strictly between them (`1/4 + 1/4 < |0 - 1| = 1`),
which is a genuine separation witness on the refutation side of `rel`. -/
example : Valid (AEquiv.apart (const 0) (const 1)) :=
  Valid.of_holds <| Trunc'.mk
    ⟨(⟨⟨1, 4, by decide⟩, by decide⟩, ⟨⟨1, 4, by decide⟩, by decide⟩), Trunc'.mk ⟨by decide⟩⟩

end Real
end Antithesis
