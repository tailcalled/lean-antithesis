import LeanAntithesis.Logic.Linear

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

/-- Recover the `String` from a name literal expression. -/
def nameOf? : Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

/-- The current goal, parsed as `(context entries, conclusion)`. -/
def getSeqGoal : TacticM (Array (Expr × Expr) × Expr) := do
  match (← getMainTarget).getAppFnArgs with
  | (``Seq, #[Γ, G]) => return (parseCtx Γ, G)
  | _ => throwError "not a `linear` goal (expected `Seq Γ G`); run `linear` first"

/-- Enter linear proof mode from a bare entailment `A ⊢ G`. -/
elab "linear" : tactic => do
  match (← getMainTarget).getAppFnArgs with
  | (``Seq, _) => pure ()
  | (``Entails, _) => evalTactic (← `(tactic| refine Seq.ofEntails (n := "this") ?_))
  | _ => throwError "`linear` expects a goal of the form `A ⊢ G`"

/-- Name the head resource (1 name) or split a head `⊗` into two named pieces. -/
elab "lintro" names:(colGt ident)+ : tactic => do
  let (Γ, G) ← getSeqGoal
  if Γ.isEmpty then throwError "no resource to introduce"
  let ns := names.map (·.getId.toString)
  match ns.size with
  | 1 =>
    -- surgically rename the head resource (preserving universes), then `change`
    match (← getMainTarget).getAppFnArgs with
    | (``Seq, #[Γraw, _]) =>
      match Γraw.getAppFnArgs with
      | (``LCtx.cons, #[_, res, rest]) =>
        let newΓ := mkAppN Γraw.getAppFn #[mkStrLit ns[0]!, res, rest]
        let Γstx ← newΓ.toSyntax
        let Gstx ← G.toSyntax
        evalTactic (← `(tactic| change Seq $Γstx $Gstx))
      | _ => throwError "no head resource to name"
    | _ => throwError "not in linear mode"
  | 2 =>
    let n₁ := Syntax.mkStrLit ns[0]!
    let n₂ := Syntax.mkStrLit ns[1]!
    evalTactic (← `(tactic| refine Seq.split (n₁ := $n₁) (n₂ := $n₂) ?_))
  | k => throwError "lintro currently supports 1 or 2 names (got {k})"

/-- Find a resource by name; return its index (0 = head). -/
def findRes (target : String) : TacticM Nat := do
  let (Γ, _) ← getSeqGoal
  match Γ.findIdx? (fun p => nameOf? p.1 == some target) with
  | some i => return i
  | none => throwError "no resource named `{target}`"

/-- Instantiate a `⨅`-resource `h` at witness `a`. -/
elab "lspecialize" h:(colGt ident) a:(colGt term) : tactic => do
  match ← findRes h.getId.toString with
  | 0 => evalTactic (← `(tactic| refine Seq.specialize $a ?_))
  | 1 => evalTactic (← `(tactic| refine Seq.swap ?_; refine Seq.specialize $a ?_))
  | i => throwError "resource is at depth {i}; only head/second supported"

/-- Provide a witness `a` for a `⨆`-goal. -/
elab "lexists" a:(colGt term) : tactic => do
  evalTactic (← `(tactic| refine Seq.exists_intro $a ?_))

/-- Discard the resource named `h` (affine weakening). -/
elab "lweaken" h:(colGt ident) : tactic => do
  match ← findRes h.getId.toString with
  | 0 => evalTactic (← `(tactic| refine Seq.weaken ?_))
  | 1 => evalTactic (← `(tactic| refine Seq.swap ?_; refine Seq.weaken ?_))
  | i => throwError "resource is at depth {i}; only head/second supported"

/-- Finish a linear proof: strip the context's units and let the solver build
the realizer. -/
macro "lclose" : tactic =>
  `(tactic| (refine Seq.closeClean ?_; simp only [LCtx.clean]; antithesis))

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
