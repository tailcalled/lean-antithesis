import Lean.Elab.Command

/-!
# The `affineHyp` linter

Flags any declaration that takes an **entailment as an argument** — a binder of type
`_ ⊢ _` (`Antithesis.Entails`, including its `⊤ ⊢ _` special case `Valid _`).  The
antithesis discipline is that a hypothesis should live *on the sequent* a proof
produces (as a `⊗`/`⊓` resource), not be threaded in as a separate Lean-level
argument.

The fundamental combinators that manipulate entailments (`cut`, `tensor_mono`, the
`Seq.*` proof-mode primitives, `relTrans`, the congruence lifters, …) necessarily take
entailment arguments, so the linter is disabled in the files that define them with
`set_option linter.affineHyp false`.  It is meant to run on the *application* layers
(e.g. `Numbers/`).
-/

open Lean Elab Command

namespace Antithesis.Linter

register_option linter.affineHyp : Bool := {
  defValue := true
  descr := "flag declarations that take an entailment `_ ⊢ _` (or `Valid _`) as an \
argument; such a hypothesis usually belongs on the sequent instead.  Disable in files \
defining fundamental entailment combinators."
}

/-- Is `t` an entailment type — `Entails`/`⊢` or its `Valid` (`⊤ ⊢ _`) abbreviation? -/
def isEntailmentType (t : Expr) : Bool :=
  let fn := t.cleanupAnnotations.getAppFn
  -- Names are written with a single backtick (no resolution) so this module need not
  -- import — and thus cannot cycle with — the files defining `Entails`/`Valid`.
  fn.isConstOf `Antithesis.Entails || fn.isConstOf `Antithesis.Valid

/-- The name of the first entailment-typed argument of a declaration type, if any. -/
partial def entailmentArg? : Expr → Option Name
  | .forallE n d b _ => if isEntailmentType d then some n else entailmentArg? b
  | _ => none

/-- The linter: warn when a `def`/`theorem`/`instance` has an entailment argument. -/
def affineHypLinter : Linter where run := fun stx => do
  unless Linter.getLinterValue linter.affineHyp (← Linter.getLinterOptions) do return
  if (← get).messages.hasErrors then return
  unless [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind do return
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.example)).isSome then return
  let declId :=
    if stx[1].isOfKind ``Lean.Parser.Command.instance then stx[1][3][0] else stx[1][1]
  if let .missing := declId then return
  let declName : Name :=
    if let `_root_ :: rest := declId[0].getId.components then rest.foldl (· ++ ·) default
    else (← getCurrNamespace) ++ declId[0].getId
  let some info := (← getEnv).find? declName | return
  if let some bn := entailmentArg? info.type then
    Linter.logLint linter.affineHyp declId
      m!"`{declName}` takes `{bn}` (an entailment `⊢` / `Valid`) as an argument; \
prefer putting that hypothesis on the sequent it produces (a `⊗`/`⊓` resource) instead."

initialize addLinter affineHypLinter

end Antithesis.Linter
