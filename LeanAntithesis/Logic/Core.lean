import Mathlib.Tactic.Common

/-!
# The antithesis interpretation: core type

Following Mike Shulman, *Affine logic for constructive mathematics*
(arXiv:1805.07518), and the nLab page "antithesis interpretation".

An affine proposition is interpreted by a pair of **`Type`s of evidence**: an
affirmation `pos` (`P⁺`) and a refutation `neg` (`P⁻`), which are *mutually
exclusive* — there is no joint evidence, i.e. a map `pos → neg → Empty`.

We work in `Type`, not `Prop`: Lean's `Prop` is proof-irrelevant and erased, so
its existentials/disjunctions only support unique choice via nonconstructive
principles.  Propositionally-truncated `Type`s (`Trunc'`, below) keep evidence
computable and *do* support unique choice constructively.
-/

universe u v w

namespace Antithesis

/-! ## Propositional truncation, valued in `Type`

`Trunc' α` collapses `α` to a mere proposition while staying in `Type` (so it is
not erased the way `Prop` is). -/

/-- Propositional truncation of a type, valued in `Type`. -/
def Trunc' (α : Type u) : Type u := Quot (fun _ _ : α => True)

namespace Trunc'

/-- Inject a witness into the truncation. -/
def mk {α : Type u} (a : α) : Trunc' α := Quot.mk _ a

/-- Any two elements of a truncation are equal. -/
protected theorem elim_eq {α : Type u} (a b : Trunc' α) : a = b := by
  induction a using Quot.ind with | _ a =>
  induction b using Quot.ind with | _ b =>
  exact Quot.sound trivial

instance {α : Type u} : Subsingleton (Trunc' α) := ⟨Trunc'.elim_eq⟩

/-- Eliminate into a type, given the map is constant up to equality. -/
def lift {α : Type u} {β : Type v} (f : α → β) (h : ∀ a b, f a = f b) : Trunc' α → β :=
  Quot.lift f (fun a b _ => h a b)

/-- Eliminate a truncation into `Empty` (a subsingleton). -/
def toEmpty {α : Type u} (f : α → Empty) : Trunc' α → Empty :=
  lift f (fun a _ => (f a).elim)

/-- Eliminate a truncation into any subsingleton (the truncation's universal
property / constructive unique choice). -/
def elimProp {α : Type u} {β : Type v} [Subsingleton β] (f : α → β) : Trunc' α → β :=
  lift f (fun _ _ => Subsingleton.elim _ _)

/-- Functorial action. -/
def map {α : Type u} {β : Type v} (f : α → β) : Trunc' α → Trunc' β :=
  lift (fun a => mk (f a)) (fun _ _ => Subsingleton.elim _ _)

end Trunc'

/-! ## The core type -/

/-- An affine proposition in the antithesis interpretation: a `Type` of
affirming evidence `pos`, a `Type` of refuting evidence `neg`, and a witness
that they cannot be jointly inhabited.

The evidence `Type`s are **propositions** — propositionally-truncated, i.e.
subsingletons.  Being subsingletons (rather than Lean's erased `Prop`) is what
lets them support unique choice constructively, and what keeps the additive
elimination rules (`⊔`-elim, distributivity, …) valid. -/
structure AProp : Type (u + 1) where
  /-- Evidence *for* the proposition (`P⁺`). -/
  pos : Type u
  /-- Evidence *against* the proposition (`P⁻`). -/
  neg : Type u
  /-- The affirmation and refutation cannot be jointly witnessed. -/
  excl : pos → neg → Empty
  /-- `pos` is a proposition (subsingleton). -/
  [pos_prop : Subsingleton pos]
  /-- `neg` is a proposition (subsingleton). -/
  [neg_prop : Subsingleton neg]

attribute [instance] AProp.pos_prop AProp.neg_prop

namespace AProp

/-- Two affine propositions are equal once their evidence types agree (the
remaining fields are propositions or land in `Empty`, hence irrelevant). -/
@[ext]
theorem ext {P Q : AProp.{u}} (hpos : P.pos = Q.pos) (hneg : P.neg = Q.neg) : P = Q := by
  cases P with | mk pp pn pe =>
  cases Q with | mk qp qn qe =>
  subst hpos; subst hneg
  congr 1
  funext a b
  exact (pe a b).elim

end AProp

end Antithesis
