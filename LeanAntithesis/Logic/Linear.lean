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

/-- Exchange the first two resources. -/
def Seq.swap {m : String} {C : AProp.{u}} (h : Seq (.cons m C (.cons n A Γ)) G) :
    Seq (.cons n A (.cons m C Γ)) G :=
  cut (cut tensor_assoc' (cut (tensor_mono tensor_comm (Entails.refl _)) tensor_assoc)) h

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
