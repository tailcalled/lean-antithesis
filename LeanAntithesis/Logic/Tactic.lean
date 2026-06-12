import LeanAntithesis.Logic.Entail

/-!
# The `antithesis` solver

Affine goals are now `Type`-inhabitation problems (build a realizer), so the
solver is `aesop`-based rather than a propositional decision procedure.  Two
rules close the gap that plain `aesop` leaves:

* `Trunc'.mk` as a safe `apply` rule — to introduce a propositional truncation;
* `excl` as a safe `forward` rule — to derive `Empty` from joint evidence.

The connectives and `Entails` are tagged `@[aesop norm unfold]`, so `aesop`
unfolds the affine structure automatically before searching.  Unlike the old
`itauto`-based version this *constructs* the realizer, so anything it proves
carries computational content.
-/

universe u w

namespace Antithesis

-- Introduce a truncation (the `aesop` move plain search is missing).
attribute [aesop safe apply] Trunc'.mk

/-- From joint evidence, derive `Empty` (so `aesop` can close by contradiction). -/
@[aesop safe forward]
def AProp.exclForward {P : AProp.{u}} (hp : P.pos) (hn : P.neg) : Empty := P.excl hp hn

/-- Build a realizer for an affine goal (`⊢`, `Holds`, `.pos`/`.neg`, …).

First reduces `.pos`/`.neg` through the connectives to plain
`×`/`⊕`/`Trunc'`/`→`/`PUnit` over atoms, then lets `aesop` construct the term. -/
macro "antithesis" : tactic => `(tactic|
  (try simp only [Entails, Holds, Refuted,
        AProp.top_pos, AProp.top_neg, AProp.bot_pos, AProp.bot_neg,
        AProp.perp_pos, AProp.perp_neg, AProp.tensor_pos, AProp.tensor_neg,
        AProp.par_pos, AProp.par_neg, AProp.limp_pos, AProp.limp_neg,
        AProp.with_pos, AProp.with_neg, AProp.plus_pos, AProp.plus_neg,
        AProp.bang_pos, AProp.bang_neg, AProp.quest_pos, AProp.quest_neg,
        AProp.all_pos, AProp.all_neg, AProp.ex_pos, AProp.ex_neg,
        AProp.lift_pos, AProp.lift_neg] at *
   aesop))

end Antithesis
