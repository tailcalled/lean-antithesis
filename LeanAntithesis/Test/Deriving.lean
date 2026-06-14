import LeanAntithesis.Sets.Deriving

/-! Exercises the `deriving AEquiv` handler and the `aequiv` tactic from an
*importing* module (the only place the `initialize`-registered handler and
`@[aequivLemmas]` attribute are active). Covers an enum, a recursive type, a
foreign-field type, and a parameterized type — via the `deriving` clause — and
shows `aequiv` closing equality/apartness goals without `Valid.of_holds`. -/

namespace Antithesis
open scoped Antithesis

-- enum
inductive Dir where
  | up | down
  deriving AEquiv

example : Valid (AEquiv.rel Dir.up Dir.up) := by aequiv
example : Valid (AEquiv.apart Dir.up Dir.down) := by aequiv

-- recursive
inductive Bin where
  | leaf
  | node (l r : Bin)
  deriving AEquiv

example : Valid (AEquiv.rel (Bin.node .leaf .leaf) (Bin.node .leaf .leaf)) := by aequiv
example : Valid (AEquiv.apart Bin.leaf (Bin.node .leaf .leaf)) := by aequiv
-- apartness deep in the structure (needs backtracking search)
example :
    Valid (AEquiv.apart (Bin.node .leaf (.node .leaf .leaf))
                        (Bin.node .leaf .leaf)) := by aequiv

-- foreign field: `Labeled` carries a `Dir`, whose `AEquiv` was derived above
inductive Labeled where
  | cons (d : Dir) (rest : Labeled)
  | nil
  deriving AEquiv

example : Valid (AEquiv.rel Labeled.nil Labeled.nil) := by aequiv
example :
    Valid (AEquiv.apart (Labeled.cons .up .nil) (Labeled.cons .down .nil)) := by aequiv

-- parameterized: `MyList α` needs `[AEquiv α]`, composing the element relation —
-- no `DecidableEq` required, so it would work for `α` a function type too
inductive MyList (α : Type u) where
  | nil
  | cons (a : α) (as : MyList α)
  deriving AEquiv

example : Valid (AEquiv.rel (MyList.nil : MyList Dir) .nil) := by aequiv
example : Valid (AEquiv.apart (MyList.cons Dir.up .nil) MyList.nil) := by aequiv
-- element apart, and element apart in the tail (backtracking past the head)
example :
    Valid (AEquiv.apart (MyList.cons Dir.up .nil) (MyList.cons Dir.down .nil)) := by aequiv
example :
    Valid (AEquiv.apart (MyList.cons Dir.up (.cons Dir.up .nil))
                        (MyList.cons Dir.up (.cons Dir.down .nil))) := by aequiv

-- tactic-built proofs are still computable + constructive (axioms: only `Quot.sound`)
def myListDemo : (AEquiv.rel (MyList.cons Dir.up .nil) (MyList.cons Dir.up .nil)).pos :=
  Valid.holds (by aequiv)
#print axioms myListDemo

/-! `aequiv` is not limited to `Valid` (`𝟙 ⊢ ·`): a concrete fact weakens into any
context, so it discharges a sequent goal `Γ ⊢ ·` with arbitrary hypotheses. -/
example (Γ : AProp) : Γ ⊢ AEquiv.rel Dir.up Dir.up := by aequiv
example (Γ : AProp) : Γ ⊢ AEquiv.apart Dir.up Dir.down := by aequiv
example (Γ : AProp) :
    Γ ⊢ AEquiv.apart (MyList.cons Dir.up .nil) (MyList.cons Dir.down .nil) := by aequiv
-- and on a bare `Holds` goal
example : Holds (AEquiv.apart Bin.leaf (Bin.node .leaf .leaf)) := by aequiv

end Antithesis
