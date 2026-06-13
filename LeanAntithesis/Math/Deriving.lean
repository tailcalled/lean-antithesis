import LeanAntithesis.Math.Equivalence

/-!
# `deriving AEquiv` (work in progress)

Metaprogramming to generate, for a plain inductive type, the structural
`AEquiv` instance following the pattern validated in `Test/Setoid.lean`:

* two inductive families — structural equality `AEq` and apartness `Apart`;
* the exclusion `excl : AEq a b → Apart a b → Empty`;
* the six recursive proof-helpers (`eqRefl/eqSymm/eqTrans`, `apSymm`,
  `apSubstL/apSubstR`);
* the `AEquiv` instance, assembled by `AProp.ofTypes` / `ofTypes_mono` /
  `ofTypes_tensor`.

Each constructor field is classified as **recursive** (the inductive itself) or
**foreign** (handled through its own `[AEquiv _]`).  Type parameters are
supported: they get `[AEquiv _]` binders, so e.g. `MyList α` derives given
`[AEquiv α]` — no `DecidableEq` needed, so it works for `α` a function type.
-/

open Lean Elab Command Meta Parser.Term

/-- Lemma set used by the `aequiv` tactic: the structural-equality / apartness
constructors of every derived type, plus `Trunc'.mk`. -/
register_label_attr aequivLemmas

namespace Antithesis

/-! ## Analysis -/

/-- One field of a constructor. -/
structure FieldInfo where
  /-- Is the field the inductive being defined (a recursive occurrence)? -/
  isRec : Bool
  /-- The field's type, as surface syntax (for binders). -/
  ty : Term
  deriving Inhabited

/-- A constructor of the inductive, with its fields classified. -/
structure CtorInfo where
  /-- Fully-qualified constructor name. -/
  name : Name
  /-- Constructor name without the type prefix (e.g. `node`). -/
  short : Name
  /-- The fields after the inductive's parameters. -/
  fields : Array FieldInfo
  deriving Inhabited

/-- Classify every constructor's fields as recursive or foreign. -/
def analyze (indVal : InductiveVal) : CommandElabM (Array CtorInfo) :=
  liftTermElabM do
    indVal.ctors.toArray.mapM fun cn => do
      let cval ← getConstInfoCtor cn
      forallTelescopeReducing cval.type fun args _ => do
        let fieldFvars := args[indVal.numParams:].toArray
        let fields ← fieldFvars.mapM fun f => do
          let ft ← inferType f
          let isRec := (← whnf ft).getAppFn.constName? == some indVal.name
          pure { isRec, ty := ← PrettyPrinter.delab ft : FieldInfo }
        pure { name := cn, short := cn.updatePrefix .anonymous, fields }

/-- `#[pfx0, pfx1, …]` of length `n`. -/
def mkArgs (n : Nat) (pfx : String) : Array Ident :=
  (Array.range n).map fun i => mkIdent (Name.mkSimple s!"{pfx}{i}")

/-! ## Inductive-family constructors -/

/-- `AEq` constructor for `C`: pointwise relatedness of the fields. -/
def mkEqCtor (eqId : Ident) (c : CtorInfo) :
    CommandElabM (TSyntax ``Lean.Parser.Command.ctor) := do
  let k := c.fields.size
  let xs := mkArgs k "x"; let ys := mkArgs k "y"
  let cid := mkIdent c.name
  let lhs ← `($cid $xs*); let rhs ← `($cid $ys*)
  let mut body ← `($eqId $lhs $rhs)
  for i in (Array.range k).reverse do
    let prem ← if (c.fields[i]!).isRec then `($eqId $(xs[i]!) $(ys[i]!))
               else `((AEquiv.rel $(xs[i]!) $(ys[i]!)).pos)
    body ← `($prem → $body)
  for i in (Array.range k).reverse do
    let ty := (c.fields[i]!).ty
    body ← `({$(ys[i]!) : $ty} → $body)
    body ← `({$(xs[i]!) : $ty} → $body)
  `(Lean.Parser.Command.ctor| | $(mkIdent c.short):ident : $body)

/-- `Apart` constructor for a *constructor mismatch* `Apart (Cᵢ x⃗) (Cⱼ y⃗)`. -/
def mkMismatchCtor (apId : Ident) (ci cj : CtorInfo) :
    CommandElabM (TSyntax ``Lean.Parser.Command.ctor) := do
  let ki := ci.fields.size; let kj := cj.fields.size
  let xs := mkArgs ki "x"; let ys := mkArgs kj "y"
  let lhs ← `($(mkIdent ci.name) $xs*); let rhs ← `($(mkIdent cj.name) $ys*)
  let mut body ← `($apId $lhs $rhs)
  for i in (Array.range kj).reverse do
    body ← `({$(ys[i]!) : $((cj.fields[i]!).ty)} → $body)
  for i in (Array.range ki).reverse do
    body ← `({$(xs[i]!) : $((ci.fields[i]!).ty)} → $body)
  let cn := mkIdent (Name.mkSimple s!"{ci.short}_{cj.short}")
  `(Lean.Parser.Command.ctor| | $cn:ident : $body)

/-- `Apart` constructor for *position `p` apart* of constructor `C`. -/
def mkFieldApartCtor (apId : Ident) (c : CtorInfo) (p : Nat) :
    CommandElabM (TSyntax ``Lean.Parser.Command.ctor) := do
  let k := c.fields.size
  let xs := mkArgs k "x"; let ys := mkArgs k "y"
  let lhs ← `($(mkIdent c.name) $xs*); let rhs ← `($(mkIdent c.name) $ys*)
  let mut body ← `($apId $lhs $rhs)
  let prem ← if (c.fields[p]!).isRec then `($apId $(xs[p]!) $(ys[p]!))
             else `((AEquiv.rel $(xs[p]!) $(ys[p]!)).neg)
  body ← `($prem → $body)
  for i in (Array.range k).reverse do
    body ← `({$(ys[i]!) : $((c.fields[i]!).ty)} → $body)
  for i in (Array.range k).reverse do
    body ← `({$(xs[i]!) : $((c.fields[i]!).ty)} → $body)
  let cn := mkIdent (Name.mkSimple s!"{c.short}_{p}")
  `(Lean.Parser.Command.ctor| | $cn:ident : $body)

/-! ## The command -/

/-- Generate the structural `AEquiv` instance for an inductive (whose parameters,
if any, are themselves types carrying `AEquiv`). -/
def deriveAEquiv (indName : Name) : CommandElabM Unit := do
  let indVal ← liftTermElabM <| getConstInfoInduct indName
  let ctors ← analyze indVal
  let Tid := mkIdent indName
  let curr ← getCurrNamespace
  -- parameters: binders `{α : _}` / `[AEquiv α]`, the applied type `T α …`, and
  -- the family's result sort (`Type u`).  All empty/`Tid`/`Type` when paramless.
  let (binders, TApp, sortStx) ← liftTermElabM <|
    forallTelescopeReducing indVal.type fun ps res => do
      let mut bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      let mut pids : Array Term := #[]
      for p in ps do
        let pid := mkIdent (← p.fvarId!.getUserName)
        let pty ← inferType p
        bs := bs.push (← `(bracketedBinder| {$pid : $(← PrettyPrinter.delab pty)}))
        if pty.isSort then bs := bs.push (← `(bracketedBinder| [AEquiv $pid]))
        pids := pids.push pid
      return (bs, ← `($Tid $pids*), ← PrettyPrinter.delab res)
  -- relative names (resolve within the current namespace)
  let rel (suffix : Name) : Name := (indName ++ suffix).replacePrefix curr .anonymous
  let eqId := mkIdent (rel `AEq)
  let apId := mkIdent (rel `Apart)
  let exclId := mkIdent (rel `aeqExcl)
  let eqReflId := mkIdent (rel `aeqRefl)
  let eqSymmId := mkIdent (rel `aeqSymm)
  let eqTransId := mkIdent (rel `aeqTrans)
  let apSymmId := mkIdent (rel `apSymm)
  let apSubstLId := mkIdent (rel `apSubstL)
  let apSubstRId := mkIdent (rel `apSubstR)
  -- constructor idents of the two families
  let eqCtor (c : CtorInfo) : Ident := mkIdent (rel (`AEq ++ c.short))
  let apMis (ci cj : CtorInfo) : Ident :=
    mkIdent (rel (`Apart ++ Name.mkSimple s!"{ci.short}_{cj.short}"))
  let apFld (c : CtorInfo) (p : Nat) : Ident :=
    mkIdent (rel (`Apart ++ Name.mkSimple s!"{c.short}_{p}"))
  -- 1. the AEq inductive
  let eqCtors ← ctors.mapM (mkEqCtor eqId ·)
  elabCommand (← `(inductive $eqId $binders:bracketedBinder* :
    $TApp → $TApp → $sortStx where $eqCtors*))
  -- 2. the Apart inductive
  let mut apCtors : Array (TSyntax ``Lean.Parser.Command.ctor) := #[]
  for ci in ctors do for cj in ctors do
    if ci.short != cj.short then apCtors := apCtors.push (← mkMismatchCtor apId ci cj)
  for c in ctors do for p in [0:c.fields.size] do
    apCtors := apCtors.push (← mkFieldApartCtor apId c p)
  elabCommand (← `(inductive $apId $binders:bracketedBinder* :
    $TApp → $TApp → $sortStx where $apCtors*))
  -- tag both families' constructors so the `aequiv` tactic can find them
  let mut ctorIds : Array Ident := ctors.map eqCtor
  for ci in ctors do for cj in ctors do
    if ci.short != cj.short then ctorIds := ctorIds.push (apMis ci cj)
  for c in ctors do for p in [0:c.fields.size] do ctorIds := ctorIds.push (apFld c p)
  elabCommand (← `(attribute [aequivLemmas] $ctorIds*))
  -- helper: a `private def name : ty := fun args => match args with alts`
  let mkDef (name : Ident) (ty : Term) (args : Array Ident)
      (alts : Array (TSyntax ``Lean.Parser.Term.matchAlt)) : CommandElabM Unit := do
    let discrs : Array (TSyntax ``Lean.Parser.Term.matchDiscr) ←
      args.mapM fun a => `(matchDiscr| $a:term)
    elabCommand (← `(private def $name:ident $binders:bracketedBinder* : $ty :=
      fun $args* => match $[$discrs],* with $alts:matchAlt*))
  let wild (n : Nat) : CommandElabM (Array Term) := (Array.range n).mapM fun _ => `(_)
  let he := mkIdent (Name.mkSimple "he")
  let hh := mkIdent (Name.mkSimple "h")
  let ap := mkIdent (Name.mkSimple "ap")
  -- 3. excl : {a b} → AEq a b → Apart a b → Empty
  let mut exclAlts := #[]
  for c in ctors do
    if c.fields.size == 0 then
      exclAlts := exclAlts.push (← `(matchAltExpr| | $(eqCtor c), $ap => nomatch $ap))
    else
      for p in [0:c.fields.size] do
        let mut hes ← wild c.fields.size
        hes := hes.set! p he
        let pe ← `($(eqCtor c) $hes*)
        let rhs ← if (c.fields[p]!).isRec then `($exclId $he $hh)
                  else `((AEquiv.rel _ _).excl $he $hh)
        exclAlts := exclAlts.push
          (← `(matchAltExpr| | $pe, $(apFld c p) $hh => $rhs))
  mkDef exclId (← `({a b : $TApp} → $eqId a b → $apId a b → Empty))
    #[mkIdent `e, mkIdent `p] exclAlts
  -- 4. eqRefl : (l : T) → AEq l l
  let mut reflAlts := #[]
  for c in ctors do
    let xs := mkArgs c.fields.size "x"
    let pat ← `($(mkIdent c.name) $xs*)
    let rhsArgs ← (Array.range c.fields.size).mapM fun i =>
      if (c.fields[i]!).isRec then `($eqReflId $(xs[i]!))
      else `(Valid.holds (AEquiv.refl $(xs[i]!)))
    let rhs ← `($(eqCtor c) $rhsArgs*)
    reflAlts := reflAlts.push (← `(matchAltExpr| | $pat => $rhs))
  mkDef eqReflId (← `((l : $TApp) → $eqId l l)) #[mkIdent `l] reflAlts
  -- 5. eqSymm : {a b} → AEq a b → AEq b a
  let mut symmEqAlts := #[]
  for c in ctors do
    let hs := mkArgs c.fields.size "h"
    let pat ← `($(eqCtor c) $hs*)
    let rhsArgs ← (Array.range c.fields.size).mapM fun i =>
      if (c.fields[i]!).isRec then `($eqSymmId $(hs[i]!))
      else `((AEquiv.symm _ _).1 $(hs[i]!))
    let rhs ← `($(eqCtor c) $rhsArgs*)
    symmEqAlts := symmEqAlts.push (← `(matchAltExpr| | $pat => $rhs))
  mkDef eqSymmId (← `({a b : $TApp} → $eqId a b → $eqId b a)) #[mkIdent `e] symmEqAlts
  -- 6. eqTrans : {a b c} → AEq a b → AEq b c → AEq a c
  let mut transEqAlts := #[]
  for c in ctors do
    let hs := mkArgs c.fields.size "h"; let gs := mkArgs c.fields.size "g"
    let p1 ← `($(eqCtor c) $hs*); let p2 ← `($(eqCtor c) $gs*)
    let rhsArgs ← (Array.range c.fields.size).mapM fun i =>
      if (c.fields[i]!).isRec then `($eqTransId $(hs[i]!) $(gs[i]!))
      else `((AEquiv.trans _ _ _).1 ($(hs[i]!), $(gs[i]!)))
    let rhs ← `($(eqCtor c) $rhsArgs*)
    transEqAlts := transEqAlts.push
      (← `(matchAltExpr| | $p1, $p2 => $rhs))
  mkDef eqTransId (← `({a b c : $TApp} → $eqId a b → $eqId b c → $eqId a c))
    #[mkIdent `e, mkIdent `f] transEqAlts
  -- 7. apSymm : {a b} → Apart a b → Apart b a
  let mut apSymmAlts := #[]
  for ci in ctors do for cj in ctors do
    if ci.short != cj.short then
      apSymmAlts := apSymmAlts.push
        (← `(matchAltExpr| | $(apMis ci cj) => $(apMis cj ci)))
  for c in ctors do for p in [0:c.fields.size] do
    let rhs ← if (c.fields[p]!).isRec then `($(apFld c p) ($apSymmId $hh))
              else `($(apFld c p) ((AEquiv.symm _ _).2 $hh))
    apSymmAlts := apSymmAlts.push
      (← `(matchAltExpr| | $(apFld c p) $hh => $rhs))
  mkDef apSymmId (← `({a b : $TApp} → $apId a b → $apId b a)) #[mkIdent `p] apSymmAlts
  -- 8. apSubstL : {a b c} → AEq a b → Apart a c → Apart b c
  let mut substLAlts := #[]
  for c in ctors do
    if c.fields.size == 0 then
      substLAlts := substLAlts.push
        (← `(matchAltExpr| | $(eqCtor c), $ap => $ap))
    else
      for d in ctors do
        if d.short != c.short then
          let w ← wild c.fields.size
          substLAlts := substLAlts.push
            (← `(matchAltExpr| | $(eqCtor c) $w*, $(apMis c d) => $(apMis c d)))
      for p in [0:c.fields.size] do
        let mut hes ← wild c.fields.size
        hes := hes.set! p he
        let pe ← `($(eqCtor c) $hes*)
        let rhs ← if (c.fields[p]!).isRec then `($(apFld c p) ($apSubstLId $he $hh))
                  else `($(apFld c p) (((AEquiv.trans _ _ _).2 $hh).1 $he))
        substLAlts := substLAlts.push
          (← `(matchAltExpr| | $pe, $(apFld c p) $hh => $rhs))
  mkDef apSubstLId (← `({a b c : $TApp} → $eqId a b → $apId a c → $apId b c))
    #[mkIdent `e, mkIdent `p] substLAlts
  -- 9. apSubstR : {a b c} → AEq b c → Apart a c → Apart a b
  let mut substRAlts := #[]
  for c in ctors do
    if c.fields.size == 0 then
      substRAlts := substRAlts.push
        (← `(matchAltExpr| | $(eqCtor c), $ap => $ap))
    else
      for d in ctors do
        if d.short != c.short then
          let w ← wild c.fields.size
          substRAlts := substRAlts.push
            (← `(matchAltExpr| | $(eqCtor c) $w*, $(apMis d c) => $(apMis d c)))
      for p in [0:c.fields.size] do
        let mut hes ← wild c.fields.size
        hes := hes.set! p he
        let pe ← `($(eqCtor c) $hes*)
        let rhs ← if (c.fields[p]!).isRec then `($(apFld c p) ($apSubstRId $he $hh))
                  else `($(apFld c p) (((AEquiv.trans _ _ _).2 $hh).2 $he))
        substRAlts := substRAlts.push
          (← `(matchAltExpr| | $pe, $(apFld c p) $hh => $rhs))
  mkDef apSubstRId (← `({a b c : $TApp} → $eqId b c → $apId a c → $apId a b))
    #[mkIdent `e, mkIdent `p] substRAlts
  -- 10. the instance
  elabCommand (← `(instance $binders:bracketedBinder* : AEquiv $TApp := {
    rel := fun x y => AProp.ofTypes ($eqId x y) ($apId x y) $exclId
    refl := fun l => Valid.of_holds (Trunc'.mk ($eqReflId l))
    symm := fun _ _ => AProp.ofTypes_mono $eqSymmId $apSymmId
    trans := fun _ _ _ => AProp.ofTypes_tensor $eqTransId $apSubstLId $apSubstRId }))

/-- `derive_aequiv T` generates the structural `AEquiv T` instance. -/
elab "derive_aequiv " indId:ident : command => do
  deriveAEquiv (← liftCoreM <| realizeGlobalConstNoOverloadCore indId.getId)

/-- Hook so `inductive T … deriving AEquiv` works. -/
initialize
  registerDerivingHandler ``AEquiv fun names => do
    names.forM deriveAEquiv
    return true

/-! ## The `aequiv` tactic

Closes a concrete structural equality/apartness goal by searching for the witness
— so apartness reads as nicely as `AEquiv.refl` does for equality, with no
`Valid.of_holds`/`Trunc'.mk` plumbing.  Works on `Valid (AEquiv.rel/apart a b)`,
on `Holds`, and — since a concrete fact is valid and so weakens into any context —
on a sequent `Γ ⊢ AEquiv.rel/apart a b` with arbitrary hypotheses `Γ`.

It reduces the goal with `Entails.of_holds` (affine weakening; the `Γ = 𝟙` case is
ordinary validity) and lets `solve_by_elim` assemble the witness from the
`@[aequivLemmas]`-tagged constructors of every derived family. -/
syntax "aequiv" : tactic
macro_rules
  | `(tactic| aequiv) =>
    -- `mkIdent` keeps the attribute name unhygienic so `using` resolves it
    `(tactic| first
      | exact Entails.of_holds (AEquiv.refl _).holds
      | exact (AEquiv.refl _).holds
      | ((try apply Entails.of_holds)
         solve_by_elim (maxDepth := 32) [Trunc'.mk] using $(mkIdent `aequivLemmas)))

/-! The `derive_aequiv` command and `deriving AEquiv` clause, the `aequiv` tactic,
and the smoke tests all live in importing modules (the handler and the
`@[aequivLemmas]` attribute are `initialize`-registered, hence only active on
import); see `Test/Deriving.lean`. -/

end Antithesis
