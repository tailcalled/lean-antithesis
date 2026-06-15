import LeanAntithesis.Logic.Calculus

/-!
# Reflected linear context for the `linear` proof mode (Type-valued)

`Seq Γ G` is the proposition (now: the *data*) `⊗Γ ⊢ G`, a realizer over a named
context of resources.  The directional rules below are realizer compositions of
the calculus rules, so the proof-mode tactics only ever `refine` a proven `def`.
-/

universe u v

namespace Antithesis
open scoped Antithesis

namespace Linear

/-- A named affine context. -/
inductive LCtx : Type (u + 1) where
  | nil : LCtx
  | cons (name : String) (res : AProp.{u}) (rest : LCtx) : LCtx

/-- The tensor of all resources (right-nested, unit-terminated). -/
def LCtx.interp : LCtx.{u} → AProp.{u}
  | .nil => AProp.top
  | .cons _ A Γ => A ⊗ Γ.interp

/-- The linear sequent judgement, as realizer data. -/
def Seq (Γ : LCtx.{u}) (G : AProp.{u}) : Type u := Γ.interp ⊢ G

variable {Γ : LCtx.{u}} {A B G : AProp.{u}} {n n₁ n₂ : String}

/-- `linear` entry. -/
def Seq.ofEntails (h : Seq (.cons n A .nil) G) : A ⊢ G := cut unit_tensor h

/-- `lintro` splitting a tensor resource (⊗-left). -/
def Seq.split (h : Seq (.cons n₁ A (.cons n₂ B Γ)) G) : Seq (.cons n (A ⊗ B) Γ) G :=
  cut tensor_assoc h

/-- `lintro` on a `⊸` goal (⊸-right). -/
def Seq.introLimp (h : Seq (.cons n A Γ) B) : Seq Γ (A ⊸ B) :=
  curry (cut tensor_comm h)

/-- `lspecialize` instantiating a `⨅` resource at `a` (∀-left). -/
def Seq.specialize {α : Type u} {P : α → AProp.{u}} (a : α)
    (h : Seq (.cons n (P a) Γ) G) : Seq (.cons n (AProp.all P) Γ) G :=
  cut (tensor_mono (all_elim a) (Entails.refl _)) h

/-- `lexists` providing a witness for a `⨆` goal (∃-right). -/
def Seq.exists_intro {α : Type u} {P : α → AProp.{u}} (a : α)
    (h : Seq Γ (P a)) : Seq Γ (AProp.ex P) :=
  cut h (ex_intro a)

/-- `lweaken`: discard the head resource (affine). -/
def Seq.weaken (h : Seq Γ G) : Seq (.cons n A Γ) G :=
  cut (cut tensor_comm tensor_weaken) h

/-- Move the second tensor factor out in front: `A ⊗ (B ⊗ C) ⊢ B ⊗ (A ⊗ C)`. -/
def tensor_swap₂ {A B C : AProp.{u}} : A ⊗ (B ⊗ C) ⊢ B ⊗ (A ⊗ C) :=
  cut tensor_assoc' (cut (tensor_mono tensor_comm (Entails.refl _)) tensor_assoc)

/-- Exchange the first two resources. -/
def Seq.swap {m : String} {C : AProp.{u}} (h : Seq (.cons m C (.cons n A Γ)) G) :
    Seq (.cons n A (.cons m C Γ)) G :=
  cut tensor_swap₂ h

/-- Bring the resource at index `k` to the front of the context. -/
def LCtx.pull : Nat → LCtx.{u} → LCtx.{u}
  | 0, Γ => Γ
  | _ + 1, .nil => .nil
  | k + 1, .cons n A rest =>
    match rest.pull k with
    | .nil => .cons n A .nil
    | .cons m B rest' => .cons m B (.cons n A rest')

/-- Pulling a resource forward is a permutation, so the tensors are interchangeable. -/
def LCtx.pull_interp : (k : Nat) → (Γ : LCtx.{u}) → Γ.interp ⊢ (Γ.pull k).interp
  | 0, _ => Entails.refl _
  | _ + 1, .nil => Entails.refl _
  | k + 1, .cons _ A rest => by
    have ih : rest.interp ⊢ (rest.pull k).interp := pull_interp k rest
    cases hc : rest.pull k with
    | nil =>
      simp only [LCtx.pull, hc, LCtx.interp]; rw [hc] at ih
      exact tensor_mono (Entails.refl A) ih
    | cons m B rest' =>
      simp only [LCtx.pull, hc, LCtx.interp]; rw [hc] at ih
      exact cut (tensor_mono (Entails.refl A) ih) tensor_swap₂

/-- Reduce a goal to one where resource `k` has been pulled to the head. -/
def Seq.pullToFront (k : Nat) (h : Seq (Γ.pull k) G) : Seq Γ G :=
  cut (LCtx.pull_interp k Γ) h

/-- `lmap` on the head resource: rewrite it forward along an entailment. -/
def Seq.mapHead (e : A ⊢ B) (h : Seq (.cons n B Γ) G) : Seq (.cons n A Γ) G :=
  cut (tensor_mono e (Entails.refl _)) h

/-- `lmap` on the second resource. -/
def Seq.mapSnd {m : String} {C D : AProp.{u}} (e : C ⊢ D)
    (h : Seq (.cons n A (.cons m D Γ)) G) : Seq (.cons n A (.cons m C Γ)) G :=
  cut (tensor_mono (Entails.refl A) (tensor_mono e (Entails.refl Γ.interp))) h

/-- `lcut`: rewrite the goal backward along an entailment `G' ⊢ G`. -/
def Seq.cutGoal {G' : AProp.{u}} (e : G' ⊢ G) (h : Seq Γ G') : Seq Γ G := cut h e

/-- `lhave`: introduce an established fact `Q` (a `Valid Q = ⊤ ⊢ Q`) as a new head
resource — bringing closed/conditionally-proven facts into the context. -/
def Seq.haveR {Q : AProp.{u}} (e : AProp.top ⊢ Q) (k : Seq (.cons n Q Γ) G) : Seq Γ G :=
  cut (cut unit_tensor (cut tensor_comm (tensor_mono e (Entails.refl _)))) k

/-- `lcombine`: consume the head two resources `A`, `B` with a binary entailment
`e : A ⊗ B ⊢ C`, replacing them by a single resource `C`.  This is how a
multi-assumption lemma is applied inside the proof mode. -/
def Seq.combine {n₁ n₂ : String} {C : AProp.{u}} (e : A ⊗ B ⊢ C)
    (k : Seq (.cons n C Γ) G) : Seq (.cons n₁ A (.cons n₂ B Γ)) G :=
  cut (cut tensor_assoc' (tensor_mono e (Entails.refl _))) k

/-- `lwith`: split a `⊓`-goal into two subgoals over the **same** context (the
additive/cartesian rule — the context is shared, not divided). -/
def Seq.withIntro {P Q : AProp.{u}} (h₁ : Seq Γ P) (h₂ : Seq Γ Q) : Seq Γ (P ⊓ Q) :=
  with_intro h₁ h₂

/-- The unit-free tensor of the resources (no trailing `⊗ ⊤`). -/
def LCtx.clean : LCtx.{u} → AProp.{u}
  | .nil => AProp.top
  | .cons _ A .nil => A
  | .cons _ A Γ => A ⊗ Γ.clean

/-- The full interpretation entails the unit-free one (strips trailing units). -/
def interp_entails_clean : (Γ : LCtx.{u}) → Γ.interp ⊢ Γ.clean
  | .nil => Entails.refl _
  | .cons _ _ .nil => tensor_unit
  | .cons _ A (.cons m B Γ) => tensor_mono (Entails.refl A) (interp_entails_clean (.cons m B Γ))

/-- Closing: reduce `Seq Γ G` to the underlying entailment. -/
def Seq.close (h : Γ.interp ⊢ G) : Seq Γ G := h

/-- Closing through the unit-free context (cleaner leaf for the solver). -/
def Seq.closeClean (h : Γ.clean ⊢ G) : Seq Γ G := cut (interp_entails_clean Γ) h

/-- Reshape the context to any `Γ'` whose tensor is entailed by the current one. -/
def Seq.changeCtx {Γ Γ' : LCtx.{u}} (reassoc : Γ.interp ⊢ Γ'.interp) (h : Seq Γ' G) : Seq Γ G :=
  cut reassoc h

end Linear
end Antithesis
