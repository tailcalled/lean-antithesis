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
* `lmap h e` — rewrite resource `h` forward along an entailment `e : A ⊢ A'`.
* `lcut e` — rewrite the goal backward along `e : G' ⊢ G` (cut on the right).
* `lhave h e` — add `h : Q` to the context from a fact `e : Valid Q`.
* `lcombine h h₁ h₂ e` — apply a binary lemma `e : A ⊗ B ⊢ C` to the resources
  named `h₁`, `h₂` (any positions), replacing them by `h : C`.
* `lwith` — split a `⊓`-goal into two subgoals over the same context.
* `lproj h fst`/`lproj h snd` — project a `⊓`-resource to one component.
* `lswap` — exchange the head two resources (rarely needed).
* `lweaken h` — discard a resource (affine).
* `lclose` — finish: hand the propositional residue to the `antithesis` solver.
* `lexact e` — finish with an explicit entailment `e : (resources) ⊢ G`.

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

/-- Enter linear proof mode from a bare entailment `A ⊢ G` (also sees through
reducible wrappers like `Valid A = ⊤ ⊢ A`). -/
elab "linear" : tactic => do
  match (← whnfR (← getMainTarget)).getAppFnArgs with
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

/-- Bring the resource named `target` to the head of the context (no-op if already
there).  Resources are addressed by name; the tactic handles the reordering. -/
def pullToHead (target : String) : TacticM Unit := do
  match ← findRes target with
  | 0 => pure ()
  | i =>
    let iStx := Syntax.mkNatLit i
    evalTactic (← `(tactic| refine Seq.pullToFront $iStx ?_; dsimp only [LCtx.pull]))

/-- Instantiate a `⨅`-resource `h` at witness `a`. -/
elab "lspecialize" h:(colGt ident) a:(colGt term) : tactic => do
  pullToHead h.getId.toString
  evalTactic (← `(tactic| refine Seq.specialize $a ?_))

/-- Provide a witness `a` for a `⨆`-goal. -/
elab "lexists" a:(colGt term) : tactic => do
  evalTactic (← `(tactic| refine Seq.exists_intro $a ?_))

/-- Rewrite a resource `h` forward along an entailment `e : A ⊢ A'`. -/
elab "lmap" h:(colGt ident) e:(colGt term) : tactic => do
  pullToHead h.getId.toString
  evalTactic (← `(tactic| refine Seq.mapHead $e ?_))

/-- Use a **duplicable** (`!`-)resource without consuming it: from `h : !P`, keep `h : !P`
and add a fresh derelicted copy `hp : P`.  The contraction/dereliction is handled for you —
this is how a `!`-hypothesis is reused (e.g. across the steps of an induction) in the
otherwise affine context.  `lweaken h` discards it when no longer needed. -/
elab "ldup" h:(colGt ident) hp:(colGt ident) : tactic => do
  pullToHead h.getId.toString
  -- `!P  ⊢  !P ⊗ P`  (contract, then derelict the second copy), then split the two off
  evalTactic (← `(tactic| refine Seq.mapHead (Antithesis.cut Antithesis.bang_contract
    (Antithesis.tensor_mono (Antithesis.Entails.refl _) Antithesis.derelict)) ?_))
  let n₁ := Syntax.mkStrLit h.getId.toString
  let n₂ := Syntax.mkStrLit hp.getId.toString
  evalTactic (← `(tactic| refine Seq.split (n₁ := $n₁) (n₂ := $n₂) ?_))

/-- Rewrite the goal backward along an entailment `e : G' ⊢ G` (cut on the right). -/
elab "lcut" e:(colGt term) : tactic => do
  evalTactic (← `(tactic| refine Seq.cutGoal $e ?_))

/-- Introduce an established fact as a new head resource: `lhave h e` with
`e : Valid Q` adds `h : Q` to the context.  This is how positivity (or any
conditionally-proven fact) enters the sequent. -/
elab "lhave" h:(colGt ident) e:(colGt term) : tactic => do
  let nm := Syntax.mkStrLit h.getId.toString
  evalTactic (← `(tactic| refine Seq.haveR (n := $nm) $e ?_))

/-- Apply a binary lemma `e : A ⊗ B ⊢ C` to the resources named `h₁` and `h₂`
(in any positions), replacing them by one resource `h : C`.  The reordering is
automatic — you only name the hypotheses. -/
elab "lcombine" h:(colGt ident) h₁:(colGt ident) h₂:(colGt ident) e:(colGt term) : tactic => do
  pullToHead h₂.getId.toString      -- h₂ to the front …
  pullToHead h₁.getId.toString      -- … then h₁, leaving the context as [h₁, h₂, …]
  let nm := Syntax.mkStrLit h.getId.toString
  evalTactic (← `(tactic| refine Seq.combine (n := $nm) $e ?_))

/-- Split a `⊓`-goal `… ⊢ P ⊓ Q` into two subgoals `… ⊢ P` and `… ⊢ Q`, each over
the same context (additive/cartesian — the context is shared).  Combined with
`lcut`, this proves congruence goals natively: `lcut add_cong; lwith; …`. -/
elab "lwith" : tactic => do
  evalTactic (← `(tactic| refine Seq.withIntro ?_ ?_))

/-- Project a `⊓`-resource `h : P ⊓ Q` to one component: `lproj h fst` keeps `P`,
`lproj h snd` keeps `Q` (discarding the other — `⊓` has no contraction). -/
elab "lproj" h:(colGt ident) side:(colGt ident) : tactic => do
  pullToHead h.getId.toString
  let proj ← match side.getId.toString with
    | "fst" => `(Antithesis.with_fst)
    | "snd" => `(Antithesis.with_snd)
    | s => throwError "lproj: side must be `fst` or `snd`, got `{s}`"
  evalTactic (← `(tactic| refine Seq.mapHead $proj ?_))

/-- Exchange the head two resources (rarely needed — `lcombine`/`lmap` reorder
by name automatically). -/
elab "lswap" : tactic => do
  evalTactic (← `(tactic| refine Seq.swap ?_))

/-- Finish by handing an explicit entailment `e : (resources) ⊢ G` to close. -/
elab "lexact" e:(colGt term) : tactic => do
  evalTactic (← `(tactic| refine Seq.closeClean ?_; simp only [LCtx.clean]; exact $e))

/-- Discard the resource named `h` (affine weakening). -/
elab "lweaken" h:(colGt ident) : tactic => do
  pullToHead h.getId.toString
  evalTactic (← `(tactic| refine Seq.weaken ?_))

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
