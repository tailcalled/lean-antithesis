import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic
import LeanAntithesis.Sets.Equivalence
import LeanAntithesis.Logic.AffineLint

/-!
# The reals as an affine set

A constructive real is its own **approximation function** `approx : ℚ⁺ → ℚ` with a
regularity bound `|approx ε - approx δ| ≤ ε + δ` (`approx ε` pins the value to
precision `ε`).  This is where the antithesis interpretation earns its keep:
equality is **undecidable** and **apartness is primitive**.

Equality and apartness are *one* `AProp`, assembled from the quantifier combinator —
so apartness comes for free as its refutation side:

  `rel x y := ⨅ (ε, δ) : ℚ⁺ × ℚ⁺, leAP |x ε - y δ| (ε + δ)`

where the atom `leAP a b` is `a ≤ b` with refutation `b < a`.  Unfolding:

* `x ~ y` (`pos`) is `∀ ε δ, |x ε - y δ| ≤ ε + δ` — the approximations agree;
* `x # y` (`neg`) is `∃ ε δ, ε + δ < |x ε - y δ|` — they are separated, i.e. there
  is a **rational strictly between** `x` and `y`.

The two-precision form makes equality transitive cleanly (`a ≤ b + 2γ ∀γ>0 ⇒
a ≤ b`); apartness is transported across equality by shrinking the precision.

The construction is genuinely constructive in content — a real *is* its computable
rational approximation function, with precision extraction (unlike `CauSeq`).  The
order side-conditions are discharged through Mathlib's `ℚ`, whose order foundations
happen to pull `Classical.choice` into proof terms; that is an artifact of Mathlib,
not of the construction.
-/

namespace Antithesis
open scoped Antithesis

/-- A positive rational (a precision). -/
abbrev PosRat : Type := {q : ℚ // 0 < q}

/-- A constructive real: a regular rational approximation function. -/
structure Real where
  /-- `approx ε` approximates the real to precision `ε`. -/
  approx : PosRat → ℚ
  /-- Regularity: approximations cohere. -/
  reg : ∀ ε δ : PosRat, |approx ε - approx δ| ≤ ε.1 + δ.1

namespace Real

/-- The atom `a ≤ b`, as an `AProp` whose refutation is the strict `b < a`. -/
def leAP (a b : ℚ) : AProp.{0} where
  pos := PLift (a ≤ b)
  neg := PLift (b < a)
  excl p q := absurd q.down (not_lt.mpr p.down)
  pos_prop := ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩
  neg_prop := ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

/-- Equality **and** apartness in one go: a universal of `leAP` atoms over a pair of
precisions. -/
def rel (x y : Real) : AProp.{0} :=
  AProp.all fun p : PosRat × PosRat => leAP |x.approx p.1 - y.approx p.2| (p.1.1 + p.2.1)

/-- A separation witness `ε + δ < |u ε - v δ|` refutes `u ~ v`. -/
def sepMk {u v : Real} (ε δ : PosRat) (h : ε.1 + δ.1 < |u.approx ε - v.approx δ|) :
    (rel u v).neg := Trunc'.mk ⟨(ε, δ), ⟨h⟩⟩

/-- Apartness is symmetric. -/
def sepSymm {u v : Real} (s : (rel u v).neg) : (rel v u).neg := by
  refine Trunc'.elimProp (fun q => ?_) s
  obtain ⟨⟨ε, δ⟩, hp⟩ := q
  exact sepMk δ ε (by rw [abs_sub_comm]; have := hp.down; linarith)

/-- The pointwise equality side is symmetric. -/
def agreeSymm {u v : Real} (h : (rel u v).pos) : (rel v u).pos :=
  fun p => ⟨by rw [abs_sub_comm]; have := (h (p.2, p.1)).down; linarith⟩

/-- Transport a separation across an equality on the left: if `a ~ b` and `a # c`,
then `b # c` (shrink the precision to `(|a ε - c δ| - ε - δ)/3`). -/
def sepShiftL {a b c : Real} (hab : (rel a b).pos) (s : (rel a c).neg) : (rel b c).neg := by
  refine Trunc'.elimProp (fun q => ?_) s
  obtain ⟨⟨ε, δ⟩, hp⟩ := q
  have hsep := hp.down
  refine sepMk ⟨(|a.approx ε - c.approx δ| - (ε.1 + δ.1)) / 3, by linarith⟩ δ ?_
  set ε' : PosRat := ⟨(|a.approx ε - c.approx δ| - (ε.1 + δ.1)) / 3, by linarith⟩ with hε'
  have hval : ε'.1 = (|a.approx ε - c.approx δ| - (ε.1 + δ.1)) / 3 := rfl
  have h1 := (hab (ε, ε')).down
  have tri := abs_sub_le (a.approx ε) (b.approx ε') (c.approx δ)
  linarith

/-- `a ≤ b` from `a ≤ b + η` for all `η > 0` — constructively, via decidability of
`≤` on `ℚ` (no `Classical`, unlike `le_of_forall_pos_le_add`). -/
private theorem qle_of_forall_pos {a b : ℚ} (h : ∀ η : ℚ, 0 < η → a ≤ b + η) : a ≤ b :=
  if hle : a ≤ b then hle
  else
    have hba : b < a := not_le.mp hle
    absurd (h ((a - b) / 2) (by linarith)) (not_le.mpr (by linarith))

instance : AEquiv Real where
  rel := rel
  refl x := Valid.of_holds fun p => ⟨x.reg p.1 p.2⟩
  symm _ _ := ⟨agreeSymm, sepSymm⟩
  trans x y z :=
    ⟨fun pq p => ⟨qle_of_forall_pos fun η hη => by
        have h1 := (pq.1 (p.1, ⟨η / 2, by linarith⟩)).down
        have h2 := (pq.2 (⟨η / 2, by linarith⟩, p.2)).down
        have tri := abs_sub_le (x.approx p.1) (y.approx ⟨η / 2, by linarith⟩) (z.approx p.2)
        linarith⟩,
     fun s => ⟨fun pxy => sepShiftL pxy s,
               fun pyz => sepSymm (sepShiftL (agreeSymm pyz) (sepSymm s))⟩⟩

/-- `ℝ` is a first-class affine set, with primitive apartness. -/
example : ASetoid := .of Real

/-- The constant real `q`. -/
def const (q : ℚ) : Real := ⟨fun _ => q, fun ε δ => by rw [sub_self, abs_zero]; linarith [ε.2, δ.2]⟩

example : Valid (AEquiv.rel (const 0) (const 0)) := AEquiv.refl _

-- `0` and `1` are apart: a rational lies strictly between them (`1/4 + 1/4 < |0 - 1|`),
-- so the separating precision is a genuine witness.
example : Valid (AEquiv.apart (const 0) (const 1)) :=
  Valid.of_holds (sepMk ⟨1/4, by norm_num⟩ ⟨1/4, by norm_num⟩ (by norm_num [const]))

end Real
end Antithesis
