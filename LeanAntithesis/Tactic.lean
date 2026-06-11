/-
Copyright (c) 2026 tailcalled. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tailcalled
-/
import LeanAntithesis.Syntax
import Mathlib.Tactic.ITauto

/-!
# The `antithesis` solver tactic

`antithesis` discharges goals about affine propositions — entailments `P ⊢ Q`,
validity `Holds P`, refutations `Refuted P`, or raw `.pos`/`.neg` claims — by:

1. adding the exclusivity fact `x⁺ → x⁻ → False` for every atom `x : AProp`
   in context (this is the bookkeeping you'd otherwise do by hand);
2. unfolding the affine connectives down to ordinary intuitionistic logic via
   the `@[simp]` projection lemmas;
3. closing the resulting goal with `itauto` (intuitionistic propositional
   logic — *not* classical `tauto`, so anything proved is constructively valid).

Goals involving the affine quantifiers `⨅`/`⨆` may need manual `intro`/witness
steps before `antithesis` finishes the propositional part.
-/

open Lean Elab Tactic Meta

namespace Antithesis

/-! `antithesis_excls` surfaces atom exclusivity (`x⁺ → x⁻ → False`) for every
`AProp` appearing in the goal, so the propositional solver can use it. -/

/-- Collect every closed `AProp`-typed subterm of `e` (atoms and compounds
alike); their exclusivity facts are what the propositional solver needs.  We do
not descend under binders, to avoid loose bound variables. -/
private partial def collectAPropAtoms (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let mut acc := acc
  if !e.hasLooseBVars then
    if (← inferType e).cleanupAnnotations.isConstOf ``AProp then
      unless acc.any (· == e) do acc := acc.push e
  match e with
  | .app f a => collectAPropAtoms a (← collectAPropAtoms f acc)
  | .mdata _ b => collectAPropAtoms b acc
  | .proj _ _ b => collectAPropAtoms b acc
  | _ => return acc

elab "antithesis_excls" : tactic => do
  liftMetaTactic fun mvarId => mvarId.withContext do
    let atoms ← collectAPropAtoms (← mvarId.getType) #[]
    let mut g := mvarId
    for a in atoms, i in [0:atoms.size] do
      let proof ← mkAppM ``AProp.excl #[a]
      let (_, g') ← g.note (Name.mkSimple s!"excl{i}") proof
      g := g'
    return [g]

/-- Reduce an affine goal to intuitionistic logic and solve it.

See the module docstring for the procedure. -/
macro "antithesis" : tactic =>
  `(tactic|
    (antithesis_excls
     try simp only [Holds, Refuted, Entails, holds_def, refuted_def, entails_def,
       AProp.top_pos, AProp.top_neg, AProp.bot_pos, AProp.bot_neg,
       AProp.perp_pos, AProp.perp_neg,
       AProp.with_pos, AProp.with_neg, AProp.plus_pos, AProp.plus_neg,
       AProp.tensor_pos, AProp.tensor_neg, AProp.par_pos, AProp.par_neg,
       AProp.limp_pos, AProp.limp_neg, AProp.bang_pos, AProp.bang_neg,
       AProp.quest_pos, AProp.quest_neg,
       AProp.all_pos, AProp.all_neg, AProp.ex_pos, AProp.ex_neg,
       AProp.lift_pos, AProp.lift_neg, toAProp_aprop, toAProp_prop] at *
     itauto))

end Antithesis
