import LeanAntithesis.Math.Deriving

/-! Exercises the `deriving AEquiv` handler from an *importing* module (the only
place an `initialize`-registered handler is active). Covers an enum, a recursive
type, and a type with a foreign field — all via the `deriving` clause. -/

namespace Antithesis
open scoped Antithesis

-- enum
inductive Dir where
  | up | down
  deriving AEquiv

example : Valid (AEquiv.rel Dir.up Dir.up) := AEquiv.refl _
example : Valid (AEquiv.apart Dir.up Dir.down) := Valid.of_holds (Trunc'.mk .up_down)

-- recursive
inductive Bin where
  | leaf
  | node (l r : Bin)
  deriving AEquiv

example : Valid (AEquiv.rel (Bin.node .leaf .leaf) (Bin.node .leaf .leaf)) := AEquiv.refl _
example : Valid (AEquiv.apart Bin.leaf (Bin.node .leaf .leaf)) :=
  Valid.of_holds (Trunc'.mk .leaf_node)

-- foreign field: `Labeled` carries a `Dir`, whose `AEquiv` was derived above
inductive Labeled where
  | cons (d : Dir) (rest : Labeled)
  | nil
  deriving AEquiv

example : Valid (AEquiv.rel Labeled.nil Labeled.nil) := AEquiv.refl _
example :
    Valid (AEquiv.apart (Labeled.cons .up .nil) (Labeled.cons .down .nil)) :=
  Valid.of_holds (Trunc'.mk (.cons_0 (Trunc'.mk .up_down)))

-- computable + constructive through a derived foreign-field instance
def labeledDemo : (AEquiv.rel (Labeled.cons .up .nil) (Labeled.cons .up .nil)).pos :=
  Valid.holds (AEquiv.refl _)

end Antithesis
