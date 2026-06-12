/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Linear

/-!
# The `linear` proof mode tactics

A `by linear; …` block proves an affine entailment in sequent style over a
named context of `AProp` resources (reflected as `Seq Γ G`).

* `linear` — enter the mode, making the hypothesis side a single resource.
* `lintro h₁ … hₙ` — split the head resource's tensor spine into named pieces
  (one name renames; two names split a `⊗`; etc.).
* `lspecialize h a` — instantiate a `⨅`-resource `h` at the witness `a`.
* `lexists a` — supply a witness for a `⨆`-goal.
* `lweaken h` — discard a resource (affine).
* `lclose` — finish: hand the propositional residue to the `antithesis` solver.

Every tactic only ever `refine`s a lemma from `Linear.lean`, so it cannot
produce an unsound proof.
-/

namespace Antithesis
open Lean Elab Tactic Meta
open scoped Antithesis

namespace Linear

/-- Parse an `LCtx` expression into its `(name, resource)` entries. -/
partial def parseCtx (e : Expr) : Array (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``LCtx.cons, #[nm, res, rest]) => #[(nm, res)] ++ parseCtx rest
  | _ => #[]

/-- Rebuild an `LCtx` expression from `(name, resource)` entries. -/
def buildCtx (pairs : Array (Expr × Expr)) : Expr :=
  pairs.foldr (fun p acc => mkApp3 (.const ``LCtx.cons []) p.1 p.2 acc) (.const ``LCtx.nil [])

/-- Recover the `String` from a name literal expression. -/
def nameOf? : Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

/-- The current goal, parsed as `(context entries, conclusion)`. -/
def getSeqGoal : TacticM (Array (Expr × Expr) × Expr) := do
  match (← getMainTarget).getAppFnArgs with
  | (``Seq, #[Γ, G]) => return (parseCtx Γ, G)
  | _ => throwError "not a `linear` goal (expected `Seq Γ G`); run `linear` first"

/-- Peel `k` tensor factors off a resource (the last factor keeps the remainder). -/
partial def peelTensor (e : Expr) (k : Nat) : TacticM (Array Expr) := do
  if k ≤ 1 then return #[e]
  match e.getAppFnArgs with
  | (``AProp.tensor, #[a, b]) => return #[a] ++ (← peelTensor b (k - 1))
  | _ => throwError "cannot split resource into {k} parts: it is not a tensor"

/-- Reshape the context to `Γ'`, discharging the propositional side condition. -/
def reshapeTo (entries : Array (Expr × Expr)) : TacticM Unit := do
  let Γ'stx ← (buildCtx entries).toSyntax
  evalTactic (← `(tactic|
    refine Seq.changeCtx (Γ' := $Γ'stx) (by simp only [LCtx.interp]; antithesis) ?_))

/-- Enter linear proof mode from a bare entailment `A ⊢ G`. -/
elab "linear" : tactic => do
  match (← getMainTarget).getAppFnArgs with
  | (``Seq, _) => pure ()
  | (``Entails, _) => evalTactic (← `(tactic| refine Seq.ofEntails (n := "this") ?_))
  | _ => throwError "`linear` expects a goal of the form `A ⊢ G`"

/-- Split the head resource's tensor spine, naming each component. -/
elab "lintro" names:(colGt ident)+ : tactic => do
  let (Γ, _) ← getSeqGoal
  if Γ.isEmpty then throwError "no resource to introduce"
  let nameStrs := names.map (·.getId.toString)
  let leaves ← peelTensor Γ[0]!.2 nameStrs.size
  let newHead := (nameStrs.zip leaves).map (fun p => (mkStrLit p.1, p.2))
  reshapeTo (newHead ++ Γ[1:].toArray)

/-- Instantiate a `⨅`-resource `h` at witness `a`. -/
elab "lspecialize" h:(colGt ident) a:(colGt term) : tactic => do
  let (Γ, _) ← getSeqGoal
  let target := h.getId.toString
  let some i := Γ.findIdx? (fun p => nameOf? p.1 == some target)
    | throwError "no resource named `{target}`"
  -- bring `h` to the head, then apply the ∀-left rule there
  reshapeTo (#[Γ[i]!] ++ Γ.eraseIdxIfInBounds i)
  evalTactic (← `(tactic| refine Seq.specialize $a ?_))

/-- Provide a witness `a` for a `⨆`-goal. -/
elab "lexists" a:(colGt term) : tactic => do
  evalTactic (← `(tactic| refine Seq.exists_intro $a ?_))

/-- Discard the resource named `h` (affine weakening). -/
elab "lweaken" h:(colGt ident) : tactic => do
  let (Γ, _) ← getSeqGoal
  let target := h.getId.toString
  let some i := Γ.findIdx? (fun p => nameOf? p.1 == some target)
    | throwError "no resource named `{target}`"
  reshapeTo (Γ.eraseIdxIfInBounds i)

/-- Finish a linear proof: discharge the propositional residue with the solver. -/
macro "lclose" : tactic =>
  `(tactic| (refine Seq.close ?_; simp only [LCtx.interp]; antithesis))

/-! ## Pretty-printing the linear goal

A `Seq Γ G` goal prints as `❲ h₁ : A₁, …, hₙ : Aₙ ⊢ₗ G ❳` instead of the raw
`LCtx.cons` chain.  This is display only. -/

/-- One displayed resource `name : resource`. -/
syntax linBinder := ident " : " term
/-- Display form of a linear sequent goal. -/
syntax (name := linSeqDisplay) "❲ " linBinder,* " ⊢ₗ " term " ❳" : term

open PrettyPrinter Delaborator SubExpr

/-- Walk the reflected context, delaborating each resource in place. -/
partial def collectCtx : DelabM (Array (String × Term)) := do
  match (← getExpr).getAppFnArgs with
  | (``LCtx.cons, #[nameE, _, _]) =>
      let resStx ← withNaryArg 1 delab
      let rest ← withNaryArg 2 collectCtx
      return #[((nameOf? nameE).getD "_", resStx)] ++ rest
  | _ => return #[]

/-- Render `Seq Γ G` as `❲ … ⊢ₗ G ❳`. -/
@[app_delab Antithesis.Linear.Seq]
def delabSeq : Delab := do
  guard <| (← getExpr).isAppOfArity ``Seq 2
  let pairs ← withNaryArg 0 collectCtx
  let g ← withNaryArg 1 delab
  let binders ← pairs.mapM fun (n, t) =>
    `(linBinder| $(mkIdent (Name.mkSimple n)):ident : $t)
  `(❲ $binders,* ⊢ₗ $g ❳)

end Linear
end Antithesis
