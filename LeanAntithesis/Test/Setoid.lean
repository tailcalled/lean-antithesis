import LeanAntithesis.Sets.Equivalence

/-! Validates the structural-apartness pattern a `deriving AEquiv` handler would
emit for a plain inductive type, and that it slots into the `AEquiv` class /
`ASetoid` bundle. -/

namespace Antithesis
open scoped Antithesis

/-- Structural equality/apartness on `Bool`: equal constructors give `⊤`,
different give `⊥`; apartness `(·)ᗮ` then says "different constructor". -/
instance : AEquiv Bool where
  rel a b := match a, b with
    | true, true => AProp.top
    | false, false => AProp.top
    | _, _ => AProp.bot
  refl b := by cases b <;> exact Entails.refl _
  symm a b := by cases a <;> cases b <;> exact Entails.refl _
  trans a b c := by cases a <;> cases b <;> cases c <;> antithesis

-- `true` and `false` are genuinely apart (constructive content, not `¬`).
example : Valid (AEquiv.apart true false) := Entails.refl _
-- equal to themselves
example : Valid (AEquiv.rel true true) := Entails.refl _
-- and `Bool` is now a first-class setoid object
example : ASetoid := ASetoid.of Bool

/-! ## Recursive case: `List`, given the element type is an `AEquiv`.

The **computable, general** encoding (the shape a `deriving` handler would emit):
affirmation (`ListEq`) and refutation (`ListApart`) are *inductive families*, so
nothing recurses into `Type`; the `AProp` is assembled by `AProp.ofTypes` and the
proofs by the `ofTypes_mono`/`ofTypes_tensor` Chu morphisms over plain recursive
helpers.  It composes from `[AEquiv α]`, so it works even for `α` a function type. -/

variable {α : Type u} [AEquiv α]

/-- Structural equality of lists: pointwise related. -/
inductive ListEq : List α → List α → Type u
  | nil : ListEq [] []
  | cons {a b as bs} : (AEquiv.rel a b).pos → ListEq as bs → ListEq (a :: as) (b :: bs)

/-- Structural apartness of lists: different length, or a position apart. -/
inductive ListApart : List α → List α → Type u
  | nilCons {b bs} : ListApart [] (b :: bs)
  | consNil {a as} : ListApart (a :: as) []
  | head {a b as bs} : (AEquiv.rel a b).neg → ListApart (a :: as) (b :: bs)
  | tail {a b as bs} : ListApart as bs → ListApart (a :: as) (b :: bs)

def listExcl : {as bs : List α} → ListEq as bs → ListApart as bs → Empty
  | _, _, .nil, ap => nomatch ap
  | _, _, .cons hp _, .head hn => (AEquiv.rel _ _).excl hp hn
  | _, _, .cons _ teq, .tail tap => listExcl teq tap

private def eqRefl : (l : List α) → ListEq l l
  | [] => .nil
  | a :: as => .cons (Valid.holds (AEquiv.refl a)) (eqRefl as)

private def eqSymm : {as bs : List α} → ListEq as bs → ListEq bs as
  | _, _, .nil => .nil
  | _, _, .cons hp teq => .cons ((AEquiv.symm _ _).1 hp) (eqSymm teq)

private def eqTrans : {as bs cs : List α} → ListEq as bs → ListEq bs cs → ListEq as cs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hp1 t1, .cons hp2 t2 => .cons ((AEquiv.trans _ _ _).1 (hp1, hp2)) (eqTrans t1 t2)

private def apSymm : {as bs : List α} → ListApart as bs → ListApart bs as
  | _, _, .nilCons => .consNil
  | _, _, .consNil => .nilCons
  | _, _, .head hn => .head ((AEquiv.symm _ _).2 hn)
  | _, _, .tail tap => .tail (apSymm tap)

-- `a ~ b` carries `a # c` to `b # c`.
private def apSubstL : {as bs cs : List α} → ListEq as bs → ListApart as cs → ListApart bs cs
  | _, _, _, .nil, ap => ap
  | _, _, _, .cons _ _, .consNil => .consNil
  | _, _, _, .cons hp _, .head hn => .head (((AEquiv.trans _ _ _).2 hn).1 hp)
  | _, _, _, .cons _ teq, .tail tap => .tail (apSubstL teq tap)

-- `b ~ c` carries `a # c` to `a # b`.
private def apSubstR : {as bs cs : List α} → ListEq bs cs → ListApart as cs → ListApart as bs
  | _, _, _, .nil, ap => ap
  | _, _, _, .cons _ _, .nilCons => .nilCons
  | _, _, _, .cons hp _, .head hn => .head (((AEquiv.trans _ _ _).2 hn).2 hp)
  | _, _, _, .cons _ teq, .tail tap => .tail (apSubstR teq tap)

instance : AEquiv (List α) where
  rel as bs := AProp.ofTypes (ListEq as bs) (ListApart as bs) listExcl
  refl l := Valid.of_holds (Trunc'.mk (eqRefl l))
  symm _ _ := AProp.ofTypes_mono eqSymm apSymm
  trans _ _ _ := AProp.ofTypes_tensor eqTrans apSubstL apSubstR

-- Computable: a `def` (not a `theorem`) using the instance needs no `noncomputable`.
def listEqDemo : (AEquiv.rel ([true] : List Bool) [true]).pos := Trunc'.mk (eqRefl _)

end Antithesis
