import LeanAntithesis.Sets.Morphism
import LeanAntithesis.Logic.Linear

/-!
# `arw` — directed rewriting for the affine equality `≈ₐ`

Lean's `rw`/`simp` only rewrite `=`/`Iff`; the affine equality `≈ₐ` is the `Type`-valued
`Valid (a ≈ₐ b)`, so neither applies.  `arw [h₁, …, hₙ]` is the analogue: it rewrites the
**left** side of a `Valid (a ≈ₐ b)` goal using each equation `hᵢ : Valid (lᵢ ≈ₐ rᵢ)` in turn
— locating `lᵢ` as a subterm, lifting the equation through the surrounding ring operations
by congruence (`addApp`/`mulApp`/`negApp`/`subApp`), and composing the steps with
transitivity — then closes by reflexivity.  This replaces hand-written
`lhave … ; lcombine … (AEquiv.trans ..)` + `addApp` chains with a single tactic call, the way
`mor` automates congruence.
-/

namespace Antithesis
open Lean Elab Tactic Meta
open scoped Antithesis

/-- Build `Valid (motive[l] ≈ₐ motive[r])` from the rule proof `rp : Valid (l ≈ₐ r)`, where
`motive` carries the loose bound variable `#0` at the rewrite occurrence(s).  Descends the
ring operations with the congruence peelers; an unchanged subterm contributes reflexivity. -/
partial def congAlong (motive rp : Expr) : MetaM Expr := do
  if motive == .bvar 0 then return rp
  if !motive.hasLooseBVar 0 then return (← mkAppM ``AEquiv.refl #[motive])
  match motive.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, y]) => mkAppM ``addApp #[← congAlong x rp, ← congAlong y rp]
  | (``HMul.hMul, #[_, _, _, _, x, y]) => mkAppM ``mulApp #[← congAlong x rp, ← congAlong y rp]
  | (``HSub.hSub, #[_, _, _, _, x, y]) => mkAppM ``subApp #[← congAlong x rp, ← congAlong y rp]
  | (``Neg.neg, #[_, _, x]) => mkAppM ``negApp #[← congAlong x rp]
  | _ => throwError "arw: cannot rewrite under `{motive}` (no congruence peeler for its head)"

/-- Extract the two sides `(a, b)` of the affine-equality conclusion `… ≈ₐ …` of a goal or
rule type (`Valid (a ≈ₐ b)`, a bare `_ ⊢ (a ≈ₐ b)`, or a proof-mode `Seq _ (a ≈ₐ b)`). -/
partial def relSides (ty : Expr) : MetaM (Expr × Expr) := do
  match (← whnfR ty).getAppFnArgs with
  | (``AEquiv.rel, #[_, _, a, b]) => return (a, b)
  | (``Entails, #[_, concl]) => relSides concl
  | (``Linear.Seq, #[_, g]) => relSides g
  | _ => throwError "arw: goal is not an affine equality `a ≈ₐ b` (got `{ty}`)"

/-- `arw [h₁, …, hₙ]` — rewrite the left side of a `Valid (a ≈ₐ b)` goal by the equations
`hᵢ`, then close by reflexivity. -/
elab "arw" "[" rules:term,* "]" : tactic => do
  for ruleStx in rules.getElems do
    let goal ← getMainGoal
    let (a, b) ← relSides (← goal.getType)
    let rp ← elabTerm ruleStx none
    let (l, r) ← relSides (← inferType rp)
    let motive ← kabstract a l
    unless motive.hasLooseBVar 0 do
      throwError "arw: `{l}` does not occur in the left-hand side `{a}`"
    let cong ← congAlong motive rp                 -- Valid (a ≈ₐ a')
    let a' := motive.instantiate1 r
    -- Replace the goal's left side `a` by `a'`, transporting along `cong` (`relCongrL`):
    -- in the proof mode this is `Seq.cutGoal`; on a bare `Valid`/`⊢` goal it is `cut`.
    let goalTy ← whnfR (← goal.getType)
    -- `(a' ≈ₐ b) ⊢ (a ≈ₐ b)`; `y := b` is pinned (it is not determined by `cong`)
    let transport ← mkAppOptM ``relCongrL #[none, none, none, none, some b, some cong]
    if goalTy.isAppOf ``Linear.Seq then
      let some Γ := goalTy.getAppArgs[0]? | throwError "arw: malformed Seq goal"
      let newGoal ← mkFreshExprMVar (← mkAppM ``Linear.Seq #[Γ, ← mkAppM ``AEquiv.rel #[a', b]])
      goal.assign (← mkAppM ``Linear.Seq.cutGoal #[transport, newGoal])
      replaceMainGoal [newGoal.mvarId!]
    else
      let newGoal ← mkFreshExprMVar (← mkAppM ``Valid #[← mkAppM ``AEquiv.rel #[a', b]])
      goal.assign (← mkAppM ``cut #[newGoal, transport])
      replaceMainGoal [newGoal.mvarId!]
  -- close if the rewritten left side now matches the right side (reflexivity from any
  -- context — works for a bare `Valid` goal and a proof-mode `Seq` goal alike)
  evalTactic (← `(tactic| first | exact Entails.of_holds (AEquiv.refl _).holds | skip))

end Antithesis
