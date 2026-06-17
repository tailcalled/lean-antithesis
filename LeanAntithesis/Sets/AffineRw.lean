import LeanAntithesis.Sets.Morphism
import LeanAntithesis.Logic.LinearTactic

/-!
# `arw` — directed rewriting for the affine equality `≈ₐ`

Lean's `rw`/`simp` only rewrite `=`/`Iff`; the affine equality `≈ₐ` is the `Type`-valued
`Valid (a ≈ₐ b)`, so neither applies.  `arw [h₁, …, hₙ]` is the analogue: it rewrites the
**left** side of an `a ≈ₐ b` goal using each equation `hᵢ` in turn — locating its left side
as a subterm, lifting it through the surrounding ring operations by congruence
(`addApp`/`mulApp`/`negApp`/`subApp`), and composing the steps with transitivity — then closes
by reflexivity.  Replaces hand-written `lhave … ; lcombine … (AEquiv.trans ..)` + `addApp`
chains, the way `mor` automates congruence.

Each `hᵢ` may be either a **closed value** `Valid (lᵢ ≈ₐ rᵢ)` or, inside the `linear` proof
mode, a **context resource** named in `Γ`: a linear `x ≈ₐ y` (consumed by the rewrite) or a
duplicable `!(x ≈ₐ y)` (a copy is taken with `ldup`, so the resource persists).
-/

/-- `@[asimp]` marks an affine rewrite rule `Valid (lhs ≈ₐ rhs)` for the `asimp` tactic — the
affine analogue of `@[simp]` (whose rules are `=`/`Iff`).  Rules rewrite left-to-right. -/
register_label_attr asimp

namespace Antithesis
open Lean Elab Tactic Meta
open scoped Antithesis

/-- Build `Valid (motive[l] ≈ₐ motive[r])` from a **closed** rule `rp : Valid (l ≈ₐ r)`. -/
partial def congAlong (motive rp : Expr) : MetaM Expr := do
  if motive == .bvar 0 then return rp
  if !motive.hasLooseBVar 0 then return (← mkAppM ``AEquiv.refl #[motive])
  match motive.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, y]) => mkAppM ``addApp #[← congAlong x rp, ← congAlong y rp]
  | (``HMul.hMul, #[_, _, _, _, x, y]) => mkAppM ``mulApp #[← congAlong x rp, ← congAlong y rp]
  | (``HSub.hSub, #[_, _, _, _, x, y]) => mkAppM ``subApp #[← congAlong x rp, ← congAlong y rp]
  | (``Neg.neg, #[_, _, x]) => mkAppM ``negApp #[← congAlong x rp]
  | _ => throwError "arw: cannot rewrite under `{motive}` (no congruence peeler for its head)"

/-- The entailment version of `congAlong`: build `(l ≈ₐ r) ⊢ (motive[l] ≈ₐ motive[r])`, used
to rewrite by a **context resource** of type `ruleTy = (l ≈ₐ r)` (the resource flows through
the rewrite occurrence; unchanged subterms contribute reflexivity from the same context). -/
partial def congAlongEnt (motive ruleTy : Expr) : MetaM Expr := do
  if motive == .bvar 0 then mkAppM ``Entails.refl #[ruleTy]
  else if !motive.hasLooseBVar 0 then
    mkAppOptM ``Entails.of_holds
      #[some ruleTy, none, some (← mkAppM ``Valid.holds #[← mkAppM ``AEquiv.refl #[motive]])]
  else match motive.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, x, y]) =>
        mkAppM ``addApp #[← congAlongEnt x ruleTy, ← congAlongEnt y ruleTy]
    | (``HMul.hMul, #[_, _, _, _, x, y]) =>
        mkAppM ``mulApp #[← congAlongEnt x ruleTy, ← congAlongEnt y ruleTy]
    | (``HSub.hSub, #[_, _, _, _, x, y]) =>
        mkAppM ``subApp #[← congAlongEnt x ruleTy, ← congAlongEnt y ruleTy]
    | (``Neg.neg, #[_, _, x]) => mkAppM ``negApp #[← congAlongEnt x ruleTy]
    | _ => throwError "arw: cannot rewrite under `{motive}` (no congruence peeler for its head)"

/-- Extract the two sides `(a, b)` of the affine-equality conclusion `… ≈ₐ …` of a goal/type. -/
partial def relSides (ty : Expr) : MetaM (Expr × Expr) := do
  match (← whnfR ty).getAppFnArgs with
  | (``AEquiv.rel, #[_, _, a, b]) => return (a, b)
  | (``Entails, #[_, concl]) => relSides concl
  | (``Linear.Seq, #[_, g]) => relSides g
  | _ => throwError "arw: goal is not an affine equality `a ≈ₐ b` (got `{ty}`)"

/-- Rewrite the goal's left side by a **closed** rule `rp : Valid (l ≈ₐ r)`. -/
def arwTerm (rp : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  -- instantiate metavariables before structural inspection: a tactic like `lwith` leaves the
  -- context/goal as an *assigned* mvar, which `getAppFnArgs`/`relSides` would otherwise miss.
  let gty ← instantiateMVars (← goal.getType)
  let (a, b) ← relSides gty
  let (l, r) ← relSides (← inferType rp)
  let motive ← kabstract a l
  unless motive.hasLooseBVar 0 do
    throwError "arw: `{l}` does not occur in the left-hand side `{a}`"
  let cong ← congAlong motive rp                                  -- Valid (a ≈ₐ a')
  let a' := motive.instantiate1 r
  let transport ← mkAppOptM ``relCongrL #[none, none, none, none, some b, some cong]
  if gty.isAppOf ``Linear.Seq then
    let some Γ := gty.getAppArgs[0]? | throwError "arw: malformed Seq goal"
    let newGoal ← mkFreshExprMVar (← mkAppM ``Linear.Seq #[Γ, ← mkAppM ``AEquiv.rel #[a', b]])
    goal.assign (← mkAppM ``Linear.Seq.cutGoal #[transport, newGoal])
    replaceMainGoal [newGoal.mvarId!]
  else
    let newGoal ← mkFreshExprMVar (← mkAppM ``Valid #[← mkAppM ``AEquiv.rel #[a', b]])
    goal.assign (← mkAppM ``cut #[newGoal, transport])
    replaceMainGoal [newGoal.mvarId!]

/-- Rewrite the goal's left side by a **context resource** `nm : resTy` (`resTy` is `x ≈ₐ y`,
or `!(x ≈ₐ y)` — then a copy is taken with `ldup` so the resource persists). -/
def arwResource (nm : String) (resTy : Expr) : TacticM Unit := do
  -- For a duplicable `!`-resource, copy out `x ≈ₐ y` (keeping the original); else use as is.
  let (workName, workTy) ←
    if resTy.isAppOf ``AProp.bang then
      let tmp := "_arwc"
      evalTactic (← `(tactic| ldup $(mkIdent (Name.mkSimple nm)) $(mkIdent (Name.mkSimple tmp))))
      pure (tmp, resTy.getAppArgs[0]!)
    else pure (nm, resTy)
  Linear.pullToHead workName
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  let (a, b) ← relSides goalTy
  let (x, _) ← relSides workTy
  let some Γ := goalTy.getAppArgs[0]? | throwError "arw: malformed Seq goal"
  let rest := Γ.getAppArgs[2]!                                    -- `cons workName workTy rest`
  let motive ← kabstract a x
  unless motive.hasLooseBVar 0 do
    throwError "arw: `{x}` does not occur in the left-hand side `{a}`"
  let liftEnt ← congAlongEnt motive workTy                        -- (x ≈ₐ y) ⊢ (a ≈ₐ a')
  -- `a'` is the rewritten side; read it off `liftEnt`'s codomain so it matches exactly.
  let (_, a') ← relSides (← inferType liftEnt)
  let newGoal ← mkFreshExprMVar (← mkAppM ``Linear.Seq #[rest, ← mkAppM ``AEquiv.rel #[a', b]])
  -- `(x≈y) ⊗ rest ⊢ (a≈a') ⊗ (a'≈b) ⊢ (a≈b)`, consuming the resource.
  let tm ← mkAppM ``tensor_mono #[liftEnt, newGoal]
  goal.assign (← mkAppM ``cut #[tm, ← mkAppM ``AEquiv.trans #[a, a', b]])
  replaceMainGoal [newGoal.mvarId!]

/-- If `ruleStx` is an identifier naming a resource in the current `Seq` context, return its
name and type; otherwise `none` (it is a closed term). -/
def resourceRule? (ruleStx : Term) : TacticM (Option (String × Expr)) := do
  match ruleStx with
  | `($id:ident) =>
    let nm := id.getId.toString
    let goalTy ← instantiateMVars (← (← getMainGoal).getType)
    unless goalTy.isAppOf ``Linear.Seq do return none
    let some Γ := goalTy.getAppArgs[0]? | return none
    for (ne, res) in Linear.parseCtx Γ do
      if Linear.nameOf? ne == some nm then return some (nm, res)
    return none
  | _ => return none

/-- `arw [h₁, …, hₙ]` — rewrite the left side of an `a ≈ₐ b` goal by the equations `hᵢ`
(closed values or context resources), then close by reflexivity. -/
elab "arw" "[" rules:term,* "]" : tactic => do
  for ruleStx in rules.getElems do
    match ← resourceRule? ruleStx with
    | some (nm, resTy) => arwResource nm resTy
    | none => arwTerm (← elabTerm ruleStx none)
  -- close if the rewritten left side now matches the right side (reflexivity from any context)
  evalTactic (← `(tactic| first | exact Entails.of_holds (AEquiv.refl _).holds | skip))

/-- Try to rewrite the goal's left side by a single `@[asimp]` rule `nm` (instantiating its
universally-quantified variables with metavariables, matched by `arwTerm`'s `kabstract`).
Returns whether it fired. -/
def tryAsimpRule (nm : Name) : TacticM Bool := do
  try
    let cst ← mkConstWithFreshMVarLevels nm
    let (mvars, _, _) ← forallMetaTelescopeReducing (← inferType cst)
    arwTerm (mkAppN cst mvars)
    pure true
  catch _ => pure false

/-- `asimp` — the affine analogue of `simp`: repeatedly rewrite the left side of an `a ≈ₐ b`
goal (closed `Valid`/`⊢` or a proof-mode `Seq`) by the `@[asimp]`-tagged affine equalities
until none fires, then close by reflexivity.  Generic over any `AEquiv` carrier. -/
elab "asimp" : tactic => do
  let names ← Lean.labelled `asimp
  for _ in [0:100] do
    let mut fired := false
    for nm in names do
      if ← tryAsimpRule nm then fired := true
    unless fired do break
  evalTactic (← `(tactic| first | exact Entails.of_holds (AEquiv.refl _).holds | skip))

end Antithesis
