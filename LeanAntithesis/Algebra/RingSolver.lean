import LeanAntithesis.Algebra.Ring
import Mathlib.Logic.Function.Iterate
import LeanAntithesis.Logic.AffineLint

/-!
# A reflective solver for affine commutative rings (`aring`)

Proof by reflection: a goal `… ⊢ rel s t` between ring expressions is decided by
reifying both sides into a syntactic `RingExpr`, normalising to a canonical polynomial,
and checking the normal forms are equal as data.  Soundness — `eval e ≈ polyEval
(norm e)` — is proved against the `ARing` axioms; the decision then needs only `rfl`
on the normal forms, and the result is weakened to the goal's antecedent.

Coefficients are kept as **signed monomials** (so `a + a` is two terms, not `2•a`),
which replaces ℤ-coefficient arithmetic with sign cancellation; and list operations
are normalised by **insertion sort**, whose soundness is a plain list induction
(`Perm.rec` cannot target the `Type`-valued `Valid`).
-/

namespace Antithesis
open scoped Antithesis

variable {R : Type} [ARing R]

namespace ARing

/-! ## Further derived equalities (proof mode), for the solver's soundness. -/

/-- `-0 ≈ 0`. -/
def neg_zero : Valid (AEquiv.rel (-(0 : R)) 0) := by
  arw [relSymm (zero_add (-(0 : R))), add_neg_cancel (0 : R)]

/-- `- -a ≈ a` (double negation). -/
def neg_neg (a : R) : Valid (AEquiv.rel (- -a) a) := by
  arw [relSymm (add_zero (- -a)), relSymm (neg_add_cancel a),
       relSymm (add_assoc (- -a) (-a) a), neg_add_cancel (-a), zero_add a]

/-- `-(a + b) ≈ -a + -b` (negation distributes over `+`, using commutativity). -/
def neg_add (a b : R) : Valid (AEquiv.rel (-(a + b)) (-a + -b)) := by
  arw [relSymm (add_zero (-(a + b))), relSymm (cancel_sum a b),
       relSymm (add_assoc (-(a + b)) (a + b) (-a + -b)),
       neg_add_cancel (a + b), zero_add (-a + -b)]
where
  /-- `(a + b) + (-a + -b) ≈ 0`. -/
  cancel_sum (a b : R) : Valid (AEquiv.rel ((a + b) + (-a + -b)) 0) := by
    arw [add_assoc a b (-a + -b), add_left_comm b (-a) (-b), add_neg_cancel b,
         add_zero (-a), add_neg_cancel a]

/-! ## Group/ring cancellation helpers and the multiplicative sign lemmas

`cancel_self`/`eq_neg_of_add_zero` transform a closed equality theorem into another, term
level, as part of the reflective ring derivations; they take `Valid` arguments by nature, so
the `affineHyp` linter is disabled for them. -/

set_option linter.affineHyp false in
/-- From `x ≈ x + x` conclude `x ≈ 0` (cancel `x` on the left). -/
def cancel_self {x : R} (h : Valid (AEquiv.rel x (x + x))) : Valid (AEquiv.rel x 0) := by
  linear; lweaken this
  lhave h0 (relSymm (neg_add_cancel x))                  -- 0 ≈ -x + x
  lhave h1 (addApp (AEquiv.refl (-x)) h)               -- -x + x ≈ -x + (x + x)
  lhave h2 (relSymm (add_assoc (-x) x x))                -- ≈ (-x + x) + x
  lhave h3 (addApp (neg_add_cancel x) (AEquiv.refl x)) -- ≈ 0 + x
  lhave h4 (zero_add x)                                  -- ≈ x
  lcombine s1 h0 h1 (AEquiv.trans ..)
  lcombine s2 s1 h2 (AEquiv.trans ..)
  lcombine s3 s2 h3 (AEquiv.trans ..)
  lcombine s4 s3 h4 (AEquiv.trans ..)                    -- 0 ≈ x
  lmap s4 (AEquiv.symm 0 x)
  lexact (Entails.refl _)

set_option linter.affineHyp false in
/-- From `x + y ≈ 0` conclude `x ≈ -y` (`x` is the additive inverse of `y`). -/
def eq_neg_of_add_zero {x y : R} (h : Valid (AEquiv.rel (x + y) 0)) :
    Valid (AEquiv.rel x (-y)) := by
  linear; lweaken this
  lhave h1 (relSymm (add_zero x))                                  -- x ≈ x + 0
  lhave h2 (addApp (AEquiv.refl x) (relSymm (add_neg_cancel y))) -- ≈ x + (y + -y)
  lhave h3 (relSymm (add_assoc x y (-y)))                          -- ≈ (x + y) + -y
  lhave h4 (addApp h (AEquiv.refl (-y)))                         -- ≈ 0 + -y
  lhave h5 (zero_add (-y))                                         -- ≈ -y
  lcombine s1 h1 h2 (AEquiv.trans ..)
  lcombine s2 s1 h3 (AEquiv.trans ..)
  lcombine s3 s2 h4 (AEquiv.trans ..)
  lcombine s4 s3 h5 (AEquiv.trans ..)
  lexact (Entails.refl _)

/-- `a * 0 ≈ 0`. -/
def mul_zero (a : R) : Valid (AEquiv.rel (a * 0) 0) :=
  cancel_self (by arw [relSymm (add_zero (0 : R)), left_distrib a 0 0])

/-- `0 * a ≈ 0`. -/
def zero_mul (a : R) : Valid (AEquiv.rel (0 * a) 0) := by arw [mul_comm 0 a, mul_zero a]

/-- `(-a) * b ≈ -(a * b)`. -/
def neg_mul (a b : R) : Valid (AEquiv.rel (-a * b) (-(a * b))) :=
  eq_neg_of_add_zero (by arw [relSymm (right_distrib (-a) a b), neg_add_cancel a, zero_mul b])

/-- `a * (-b) ≈ -(a * b)`. -/
def mul_neg (a b : R) : Valid (AEquiv.rel (a * -b) (-(a * b))) :=
  eq_neg_of_add_zero (by arw [relSymm (left_distrib a (-b) b), neg_add_cancel b, mul_zero a])

/-- `(-a) * (-b) ≈ a * b`. -/
def neg_mul_neg (a b : R) : Valid (AEquiv.rel (-a * -b) (a * b)) := by
  arw [neg_mul a (-b), mul_neg a b, neg_neg (a * b)]

/-! ## Reflected ring expressions

`RingExpr` is the syntax of the full commutative-ring fragment.  A polynomial normal
form is a list of **signed monomials** `Bool × List Nat` (`true = +`; the `List Nat`
is a product of atoms), so `a + a` is two terms, an inverse is a sign flip, and a
product concatenates monomials — sign cancellation stands in for ℤ-coefficients. -/

/-- Reflected commutative-ring expression over a `Nat`-indexed atom environment. -/
inductive RingExpr where
  | atom : Nat → RingExpr
  | zero : RingExpr
  | one : RingExpr
  | add : RingExpr → RingExpr → RingExpr
  | mul : RingExpr → RingExpr → RingExpr
  | neg : RingExpr → RingExpr

/-- Flip the sign of a signed monomial. -/
def flipSign : Bool × List Nat → Bool × List Nat := fun t => (!t.1, t.2)

/-- Interpret a reflected expression in an environment. -/
def RingExpr.eval (env : List R) : RingExpr → R
  | .atom i => env.getD i 0
  | .zero => 0
  | .one => 1
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => - a.eval env

/-- Sum of a list. -/
def sumR (l : List R) : R := l.foldr (· + ·) 0
/-- Product of a list. -/
def prodR (l : List R) : R := l.foldr (· * ·) 1

/-- Interpret a monomial (a product of atoms). -/
def monEval (env : List R) (m : List Nat) : R := prodR (m.map (fun i => env.getD i 0))

/-- Interpret a signed monomial. -/
def termEval (env : List R) : Bool × List Nat → R
  | (true, m) => monEval env m
  | (false, m) => - monEval env m

/-- Interpret a polynomial. -/
def polyEval (env : List R) (p : List (Bool × List Nat)) : R := sumR (p.map (termEval env))

/-- `sumR` turns `++` into `+`. -/
def sumR_append : (l₁ l₂ : List R) →
    Valid (AEquiv.rel (sumR (l₁ ++ l₂)) (sumR l₁ + sumR l₂))
  | [], l₂ => relSymm (zero_add (sumR l₂))
  | x :: xs, l₂ =>
    relTrans (addApp (AEquiv.refl x) (sumR_append xs l₂))
      (relSymm (add_assoc x (sumR xs) (sumR l₂)))

/-- `prodR` turns `++` into `*`. -/
def prodR_append : (l₁ l₂ : List R) →
    Valid (AEquiv.rel (prodR (l₁ ++ l₂)) (prodR l₁ * prodR l₂))
  | [], l₂ => relSymm (one_mul (prodR l₂))
  | x :: xs, l₂ =>
    relTrans (mulApp (AEquiv.refl x) (prodR_append xs l₂))
      (relSymm (mul_assoc x (prodR xs) (prodR l₂)))

/-- `monEval` turns `++` into `*`. -/
def monEval_append (env : List R) (m₁ m₂ : List Nat) :
    Valid (AEquiv.rel (monEval env (m₁ ++ m₂)) (monEval env m₁ * monEval env m₂)) := by
  simp only [monEval, List.map_append]; exact prodR_append _ _

/-- `polyEval` turns `++` into `+`. -/
def polyEval_append (env : List R) (p q : List (Bool × List Nat)) :
    Valid (AEquiv.rel (polyEval env (p ++ q)) (polyEval env p + polyEval env q)) := by
  simp only [polyEval, List.map_append]; exact sumR_append _ _

/-- A flipped signed monomial evaluates to the negation. -/
def termEval_flip (env : List R) :
    (t : Bool × List Nat) → Valid (AEquiv.rel (termEval env (flipSign t)) (- termEval env t))
  | (true, _) => AEquiv.refl _
  | (false, m) => relSymm (neg_neg (monEval env m))

/-- Negating a polynomial flips every sign. -/
def polyEval_neg (env : List R) :
    (p : List (Bool × List Nat)) →
      Valid (AEquiv.rel (-(polyEval env p)) (polyEval env (p.map flipSign)))
  | [] => neg_zero
  | t :: ts =>
    relTrans (neg_add (termEval env t) (polyEval env ts))
      (addApp (relSymm (termEval_flip env t)) (polyEval_neg env ts))

/-- Product of two signed monomials: XNOR the signs, concatenate the monomials. -/
def prodTerm : Bool × List Nat → Bool × List Nat → Bool × List Nat
  | (s₁, m₁), (s₂, m₂) => (s₁ == s₂, m₁ ++ m₂)

/-- Multiplying two signed monomials is sound. -/
def prodTerm_sound (env : List R) :
    (t u : Bool × List Nat) →
      Valid (AEquiv.rel (termEval env (prodTerm t u)) (termEval env t * termEval env u))
  | (true, m₁), (true, m₂) => monEval_append env m₁ m₂
  | (true, m₁), (false, m₂) =>
    relTrans (negApp (monEval_append env m₁ m₂))
      (relSymm (mul_neg (monEval env m₁) (monEval env m₂)))
  | (false, m₁), (true, m₂) =>
    relTrans (negApp (monEval_append env m₁ m₂))
      (relSymm (neg_mul (monEval env m₁) (monEval env m₂)))
  | (false, m₁), (false, m₂) =>
    relTrans (monEval_append env m₁ m₂)
      (relSymm (neg_mul_neg (monEval env m₁) (monEval env m₂)))

/-- Distribute a single term across a polynomial. -/
def singleDistrib (env : List R) (t : Bool × List Nat) :
    (q : List (Bool × List Nat)) →
      Valid (AEquiv.rel (polyEval env (q.map (prodTerm t))) (termEval env t * polyEval env q))
  | [] => relSymm (mul_zero (termEval env t))
  | u :: us =>
    relTrans (addApp (prodTerm_sound env t u) (singleDistrib env t us))
      (relSymm (left_distrib (termEval env t) (termEval env u) (polyEval env us)))

/-- Multiply two polynomials (all pairwise monomial products). -/
def distribute : List (Bool × List Nat) → List (Bool × List Nat) → List (Bool × List Nat)
  | [], _ => []
  | t :: ts, q => q.map (prodTerm t) ++ distribute ts q

/-- Distribution is sound. -/
def distribute_sound (env : List R) :
    (p q : List (Bool × List Nat)) →
      Valid (AEquiv.rel (polyEval env (distribute p q)) (polyEval env p * polyEval env q))
  | [], q => relSymm (zero_mul (polyEval env q))
  | t :: ts, q =>
    relTrans (polyEval_append env (q.map (prodTerm t)) (distribute ts q))
      (relTrans (addApp (singleDistrib env t q) (distribute_sound env ts q))
        (relSymm (right_distrib (termEval env t) (polyEval env ts) (polyEval env q))))

/-- Reify into the signed-monomial normal form (before sorting/cancelling). -/
def RingExpr.toPoly : RingExpr → List (Bool × List Nat)
  | .atom i => [(true, [i])]
  | .zero => []
  | .one => [(true, [])]
  | .add a b => a.toPoly ++ b.toPoly
  | .mul a b => distribute a.toPoly b.toPoly
  | .neg a => a.toPoly.map flipSign

/-- **Soundness of reification**: an expression equals its (unsorted) polynomial. -/
def RingExpr.toPoly_sound (env : List R) :
    (e : RingExpr) → Valid (AEquiv.rel (e.eval env) (polyEval env e.toPoly))
  | .atom i =>
    relTrans (relSymm (mul_one (env.getD i 0))) (relSymm (add_zero (env.getD i 0 * 1)))
  | .zero => AEquiv.refl _
  | .one => relSymm (add_zero 1)
  | .add a b =>
    relTrans (addApp (a.toPoly_sound env) (b.toPoly_sound env))
      (relSymm (polyEval_append env a.toPoly b.toPoly))
  | .mul a b =>
    relTrans (mulApp (a.toPoly_sound env) (b.toPoly_sound env))
      (relSymm (distribute_sound env a.toPoly b.toPoly))
  | .neg a => relTrans (negApp (a.toPoly_sound env)) (polyEval_neg env a.toPoly)

/-! ## Canonicalisation: sort the atoms in each monomial, sort the terms, then cancel
inverse pairs.  Only **soundness** is proved — the decision step needs `polyEval
(norm e₁) = polyEval (norm e₂)` to be `rfl`, never that `norm` is canonical, so an
over-conservative `norm` just makes `aring` incomplete, never unsound. -/

/-- Insert an atom into a monomial, ordered by index. -/
def insertNat (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js => if i ≤ j then i :: j :: js else j :: insertNat i js

/-- Inserting an atom is sound (`*` is commutative). -/
def monEval_insert (env : List R) (i : Nat) :
    (m : List Nat) →
      Valid (AEquiv.rel (monEval env (insertNat i m)) (env.getD i 0 * monEval env m))
  | [] => AEquiv.refl _
  | j :: js => by
    simp only [insertNat]
    split
    · exact AEquiv.refl _
    · exact relTrans (mulApp (AEquiv.refl (env.getD j 0)) (monEval_insert env i js))
        (mul_left_comm (env.getD j 0) (env.getD i 0) (monEval env js))

/-- Sort the atoms in a monomial. -/
def sortMon (m : List Nat) : List Nat := m.foldr insertNat []

/-- Sorting a monomial is sound. -/
def sortMon_sound (env : List R) :
    (m : List Nat) → Valid (AEquiv.rel (monEval env (sortMon m)) (monEval env m))
  | [] => AEquiv.refl _
  | i :: is =>
    relTrans (monEval_insert env i (sortMon is))
      (mulApp (AEquiv.refl (env.getD i 0)) (sortMon_sound env is))

/-- Normalising a term's monomial is sound. -/
def termEval_sortMon (env : List R) :
    (t : Bool × List Nat) → Valid (AEquiv.rel (termEval env (t.1, sortMon t.2)) (termEval env t))
  | (true, m) => sortMon_sound env m
  | (false, m) => negApp (sortMon_sound env m)

/-- Sort the atoms of every monomial in a polynomial. -/
def normMonos (p : List (Bool × List Nat)) : List (Bool × List Nat) :=
  p.map (fun t => (t.1, sortMon t.2))

/-- Normalising monomials is sound. -/
def normMonos_sound (env : List R) :
    (p : List (Bool × List Nat)) →
      Valid (AEquiv.rel (polyEval env (normMonos p)) (polyEval env p))
  | [] => AEquiv.refl _
  | t :: ts => addApp (termEval_sortMon env t) (normMonos_sound env ts)

/-- A total (lexicographic) order on monomials, for sorting terms. -/
def monLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else monLe as bs

/-- Insert a term into a polynomial, ordered by monomial. -/
def insertTerm (t : Bool × List Nat) : List (Bool × List Nat) → List (Bool × List Nat)
  | [] => [t]
  | u :: us => if monLe t.2 u.2 then t :: u :: us else u :: insertTerm t us

/-- Inserting a term is sound. -/
def insertTerm_sound (env : List R) (t : Bool × List Nat) :
    (p : List (Bool × List Nat)) →
      Valid (AEquiv.rel (polyEval env (insertTerm t p)) (termEval env t + polyEval env p))
  | [] => AEquiv.refl _
  | u :: us => by
    simp only [insertTerm]
    split
    · exact AEquiv.refl _
    · exact relTrans (addApp (AEquiv.refl (termEval env u)) (insertTerm_sound env t us))
        (add_left_comm (termEval env u) (termEval env t) (polyEval env us))

/-- Insertion sort the terms by monomial. -/
def sortTerms (p : List (Bool × List Nat)) : List (Bool × List Nat) := p.foldr insertTerm []

/-- Sorting the terms is sound. -/
def sortTerms_sound (env : List R) :
    (p : List (Bool × List Nat)) →
      Valid (AEquiv.rel (polyEval env (sortTerms p)) (polyEval env p))
  | [] => AEquiv.refl _
  | t :: ts =>
    relTrans (insertTerm_sound env t (sortTerms ts))
      (addApp (AEquiv.refl (termEval env t)) (sortTerms_sound env ts))

/-- One pass cancelling an adjacent inverse pair (same monomial, opposite sign). -/
def cancelStep : List (Bool × List Nat) → List (Bool × List Nat)
  | [] => []
  | [t] => [t]
  | t :: u :: rest =>
    if t.2 = u.2 ∧ t.1 ≠ u.1 then cancelStep rest
    else t :: cancelStep (u :: rest)

/-- An inverse pair sums to `0`. -/
def termEval_cancel (env : List R) {t u : Bool × List Nat}
    (hi : t.2 = u.2) (hs : t.1 ≠ u.1) :
    Valid (AEquiv.rel (termEval env t + termEval env u) 0) := by
  obtain ⟨st, mt⟩ := t; obtain ⟨su, mu⟩ := u
  cases st <;> cases su <;> simp_all [termEval]
  · exact neg_add_cancel _
  · exact add_neg_cancel _

/-- One cancellation pass preserves the value. -/
def cancelStep_sound (env : List R) :
    (p : List (Bool × List Nat)) →
      Valid (AEquiv.rel (polyEval env (cancelStep p)) (polyEval env p))
  | [] => AEquiv.refl _
  | [_] => AEquiv.refl _
  | t :: u :: rest => by
    simp only [cancelStep]
    split
    next hc =>
      obtain ⟨hi, hs⟩ := hc
      exact relTrans (cancelStep_sound env rest)
        (relTrans (relSymm (zero_add (polyEval env rest)))
          (relTrans (addApp (relSymm (termEval_cancel env hi hs)) (AEquiv.refl _))
            (add_assoc (termEval env t) (termEval env u) (polyEval env rest))))
    next _ =>
      exact addApp (AEquiv.refl (termEval env t)) (cancelStep_sound env (u :: rest))

/-- Iterate cancellation to a fixed point. -/
def cancel (p : List (Bool × List Nat)) : List (Bool × List Nat) := cancelStep^[p.length] p

/-- `n` cancellation passes preserve the value. -/
def iterStep_sound (env : List R) :
    (n : Nat) → (p : List (Bool × List Nat)) →
      Valid (AEquiv.rel (polyEval env (cancelStep^[n] p)) (polyEval env p))
  | 0, _ => AEquiv.refl _
  | n + 1, p => by
    rw [Function.iterate_succ_apply]
    exact relTrans (iterStep_sound env n (cancelStep p)) (cancelStep_sound env p)

/-- Iterated cancellation preserves the value. -/
def cancel_sound (env : List R) (p : List (Bool × List Nat)) :
    Valid (AEquiv.rel (polyEval env (cancel p)) (polyEval env p)) :=
  iterStep_sound env p.length p

/-! ## Normal form, decision lemma -/

/-- Canonical normal form: reify, sort monomials, sort terms, cancel. -/
def RingExpr.norm (e : RingExpr) : List (Bool × List Nat) :=
  cancel (sortTerms (normMonos e.toPoly))

/-- An expression equals its normal form. -/
def RingExpr.eval_norm (env : List R) (e : RingExpr) :
    Valid (AEquiv.rel (e.eval env) (polyEval env e.norm)) :=
  relTrans (e.toPoly_sound env)
    (relTrans (relSymm (normMonos_sound env e.toPoly))
      (relTrans (relSymm (sortTerms_sound env (normMonos e.toPoly)))
        (relSymm (cancel_sound env (sortTerms (normMonos e.toPoly))))))

/-- **The reflection principle**: equal normal forms ⇒ equal values. -/
def RingExpr.decide_eq (env : List R) (e₁ e₂ : RingExpr) (h : e₁.norm = e₂.norm) :
    Valid (AEquiv.rel (e₁.eval env) (e₂.eval env)) :=
  relTrans (e₁.eval_norm env) (by rw [h]; exact relSymm (e₂.eval_norm env))

/-! ## The `aring` tactic

Reifies the conclusion `rel s t` of the goal into `RingExpr`, closes the
unconditional identity through `decide_eq`, and weakens it (`Entails.of_holds`) to the
goal's antecedent — so it works for `Valid`, a bare `A ⊢ rel s t`, or a proof-mode
`Seq Γ (rel s t)`.  Fails (never unsoundly) if the sides don't share a normal form. -/

open Lean Elab Tactic Meta

/-- Reify a ring element into `RingExpr`, sharing the atom environment `atoms`;
`zeroE`/`oneE` are `R`'s `0`/`1`, recognised up to defeq. -/
partial def reifyRing (atoms : IO.Ref (Array Expr)) (zeroE oneE : Expr) (e : Expr) :
    MetaM Expr := do
  if ← isDefEq e zeroE then return mkConst ``RingExpr.zero
  if ← isDefEq e oneE then return mkConst ``RingExpr.one
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``RingExpr.add) (← reifyRing atoms zeroE oneE a)
        (← reifyRing atoms zeroE oneE b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``RingExpr.mul) (← reifyRing atoms zeroE oneE a)
        (← reifyRing atoms zeroE oneE b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``RingExpr.add) (← reifyRing atoms zeroE oneE a)
        (mkApp (mkConst ``RingExpr.neg) (← reifyRing atoms zeroE oneE b))
  | (``Neg.neg, #[_, _, a]) =>
      return mkApp (mkConst ``RingExpr.neg) (← reifyRing atoms zeroE oneE a)
  | (``OfNat.ofNat, #[_, n, _]) =>
      -- a numeral `k` (with `0`/`1` already handled above) is `1 + 1 + … + 0`, so that
      -- `aring` knows e.g. `2 * b ≈ b + b`.  Sound: the final `isDefEq` check rejects any
      -- carrier on which `1 + … + 0` is not defeq to the numeral.
      match n with
      | .lit (.natVal k) =>
          let mut r := mkConst ``RingExpr.zero
          for _ in [0:k] do
            r := mkApp2 (mkConst ``RingExpr.add) (mkConst ``RingExpr.one) r
          return r
      | _ => reifyAtom atoms e
  | _ => reifyAtom atoms e
where
  /-- Look up (or register) an opaque subterm as an atom. -/
  reifyAtom (atoms : IO.Ref (Array Expr)) (e : Expr) : MetaM Expr := do
    let arr ← atoms.get
    for i in [0:arr.size] do
      if ← isDefEq arr[i]! e then
        return mkApp (mkConst ``RingExpr.atom) (mkNatLit i)
    atoms.set (arr.push e)
    return mkApp (mkConst ``RingExpr.atom) (mkNatLit arr.size)

/-- Prove an affine commutative-ring equality by reflection. -/
elab "aring" : tactic => do
  let goal ← getMainGoal
  let raw ← instantiateMVars (← goal.getType)
  let (lhs, concl) ← match raw.getAppFnArgs with
    | (``Linear.Seq, #[g₁, g]) =>
        pure (mkApp (mkConst ``Linear.LCtx.interp raw.getAppFn.constLevels!) g₁, g)
    | _ => match (← whnfR raw).getAppFnArgs with
      | (``Entails, #[a, g]) => pure (a, g)
      | _ => throwError "aring: goal must be `… ⊢ AEquiv.rel _ _`"
  let some (s, t) := (match concl.getAppFnArgs with
    | (``AEquiv.rel, #[_, _, s, t]) => some (s, t)
    | _ => none) | throwError "aring: conclusion is not `AEquiv.rel _ _`"
  let R ← inferType s
  let inst ← synthInstance (mkApp (mkConst ``ARing) R)
  let zeroE ← mkAppOptM ``Zero.zero #[R, none]
  let oneE ← mkAppOptM ``One.one #[R, none]
  let atoms ← IO.mkRef (#[] : Array Expr)
  let e₁ ← reifyRing atoms zeroE oneE s
  let e₂ ← reifyRing atoms zeroE oneE t
  let arr ← atoms.get
  let envExpr ← mkListLit R arr.toList
  let n₁ := mkApp (mkConst ``RingExpr.norm) e₁
  let n₂ := mkApp (mkConst ``RingExpr.norm) e₂
  unless ← isDefEq n₁ n₂ do
    throwError "aring: the two sides are not equal as commutative-ring expressions"
  let hProof ← mkEqRefl n₁
  let valid := mkAppN (mkConst ``RingExpr.decide_eq) #[R, inst, envExpr, e₁, e₂, hProof]
  let holds ← mkAppM ``Valid.holds #[valid]
  let proof ← mkAppOptM ``Entails.of_holds #[some lhs, none, some holds]
  unless ← isDefEq (← goal.getType) (← inferType proof) do
    throwError "aring: reified expression does not match the goal"
  goal.assign proof

/-! ## Examples -/

section examples
variable {R : Type} [ARing R] (a b c : R)

-- additive group
example : Valid (AEquiv.rel ((a + b) + c) (c + (b + a))) := by aring
example : Valid (AEquiv.rel (a + -a) 0) := by aring
example : Valid (AEquiv.rel ((a + a) + (-a + -a)) 0) := by aring
example : Valid (AEquiv.rel (-(a + b)) (-b + -a)) := by aring
-- multiplication: commutativity, associativity, units, zero
example : Valid (AEquiv.rel (a * b) (b * a)) := by aring
example : Valid (AEquiv.rel ((a * b) * c) (a * (b * c))) := by aring
example : Valid (AEquiv.rel (a * 1) a) := by aring
example : Valid (AEquiv.rel (a * 0) 0) := by aring
-- distributivity and the full ring identity (a+b)*(a+b) ≈ a*a + a*b + a*b + b*b
example : Valid (AEquiv.rel (a * (b + c)) (a * b + a * c)) := by aring
example : Valid (AEquiv.rel ((a + b) * c) (c * a + b * c)) := by aring
example : Valid (AEquiv.rel ((a + b) * (a + b)) ((a * a + b * a) + (a * b + b * b))) := by aring
-- a difference of squares: (a + b) * (a - -b) ... using only + and neg for subtraction
example : Valid (AEquiv.rel ((a + b) * (a + -b)) (a * a + -(b * b))) := by aring

-- works for general sequents, not just `Valid`, by affine weakening
example (P : AProp) : P ⊢ AEquiv.rel (a * b) (b * a) := by aring
example : AEquiv.rel a a ⊢ AEquiv.rel (a * (b + c)) (a * b + a * c) := by
  linear
  aring

end examples

end ARing
end Antithesis
