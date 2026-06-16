import LeanAntithesis.Algebra.OrderedRing
import LeanAntithesis.Logic.LinearTactic
import LeanAntithesis.Logic.AffineLint

/-!
# `llinarith` — affine linear arithmetic over `AOrderedRing`

A proof-mode tactic closing `Seq Γ G` goals where the order facts are **resources in the
context `Γ`** (sequent-style, not Lean hypotheses).  It reflects the resources and goal as
linear forms over opaque atoms, searches for a nonnegative-combination certificate, and
assembles the proof from the `AOrderedRing` primitives, with ring rearrangements
discharged by `aring`.  The proof term is `Classical`-free even though the search is impure
(verified: `llinarith` proofs depend only on `[propext, Quot.sound]`).

Implemented in stages.  **Version 1** handles a goal `e ≤ₐ f` whose certificate has
coefficients in `{0,1}` with no constant slack — i.e. `f + -e` is (up to ring rearrangement)
a sum of a subset of the `yⱼ + -xⱼ` from `≤ₐ`-resources `xⱼ ≤ₐ yⱼ`.  This already covers
transitivity, chaining, and additive combinations.  The certificate is found by Gaussian
elimination (`gaussSolve`) on the per-atom linear system; later versions will add general
nonnegative-rational coefficients (Fourier–Motzkin), constant slack, and the `<ₐ`/`≈ₐ`/`⊥`
goal forms.
-/

namespace Antithesis
open scoped Antithesis
open Lean Elab Tactic Meta

namespace Linarith

/-- A linear form over atoms: a list of `(atom, coefficient)` plus a rational constant.
Atoms are compared up to `isDefEq`. -/
structure LinComb where
  /-- `(atom, coefficient)` terms. -/
  coeffs : Array (Expr × Rat)
  /-- The constant term. -/
  const : Rat
  deriving Inhabited

/-- Add a `(coefficient · atom)` to a linear form, merging defeq atoms. -/
def LinComb.addTerm (l : LinComb) (c : Rat) (atom : Expr) : MetaM LinComb := do
  if c == 0 then return l
  for h : i in [0:l.coeffs.size] do
    if ← isDefEq l.coeffs[i].1 atom then
      let (a, c0) := l.coeffs[i]
      return { l with coeffs := l.coeffs.set! i (a, c0 + c) }
  return { l with coeffs := l.coeffs.push (atom, c) }

/-- Scale a linear form by a rational. -/
def LinComb.scale (l : LinComb) (c : Rat) : LinComb :=
  { coeffs := l.coeffs.map (fun (a, x) => (a, c * x)), const := c * l.const }

/-- Add two linear forms. -/
def LinComb.add (l m : LinComb) : MetaM LinComb := do
  let mut r := { l with const := l.const + m.const }
  for (a, c) in m.coeffs do
    r ← r.addTerm c a
  return r

/-- The zero/constant forms. -/
def LinComb.ofConst (c : Rat) : LinComb := { coeffs := #[], const := c }
def LinComb.ofAtom (a : Expr) : LinComb := { coeffs := #[(a, 1)], const := 0 }

/-- Reflect a carrier expression into a linear form.  Recognises `+`, `-`(`Neg`/`HSub`),
literal scalar multiplication, `0`, `1`, numerals; everything else is an atom. -/
partial def reflect (e : Expr) : MetaM LinComb := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return (← (← reflect a).add (← reflect b))
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return (← (← reflect a).add ((← reflect b).scale (-1)))
  | (``Neg.neg, #[_, _, a]) => return (← reflect a).scale (-1)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      match natLit? a, natLit? b with
      | some n, _ => return (← reflect b).scale (n : Rat)
      | _, some n => return (← reflect a).scale (n : Rat)
      | _, _ => return LinComb.ofAtom e
  | _ =>
      match natLit? e with
      | some k => return LinComb.ofConst (k : Rat)
      | none => return LinComb.ofAtom e
where
  /-- The natural-number value of a numeral `OfNat.ofNat _ k _` (or a raw literal). -/
  natLit? (e : Expr) : Option Nat :=
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) =>
        match n with
        | .lit (.natVal k) => some k
        | _ => none
    | _ =>
        match e with
        | .lit (.natVal k) => some k
        | _ => none

/-! ## Reading order hypotheses from the sequent context, and the certificate search -/

/-- An order hypothesis read from the context: its resource name, and the linear form
`p = (reflect rhs) - (reflect lhs)` that the hypothesis asserts is `≥ 0`. -/
structure Hyp where
  /-- The resource's name in the sequent context. -/
  name : String
  /-- `rhs - lhs` as a linear form (the hypothesis says this is `≥ 0`). -/
  p : LinComb
  deriving Inhabited

/-- Parse the order resources out of a reflected `LCtx` (`(name, AProp)` pairs): a resource
of type `x ≤ₐ y` becomes a `Hyp` for `y - x ≥ 0`.  Non-order resources are returned
separately (to be weakened away). -/
def readHyps (ctx : Array (Expr × Expr)) : MetaM (Array Hyp × Array String) := do
  let mut hyps := #[]
  let mut others := #[]
  for (nmE, ty) in ctx do
    let some nm := nameOf? nmE | continue
    match ty.getAppFnArgs with
    | (``AOrd.le, #[_, _, x, y]) =>
        let p ← (← reflect y).add ((← reflect x).scale (-1))
        hyps := hyps.push { name := nm, p }
    | _ => others := others.push nm
  return (hyps, others)
where
  nameOf? : Expr → Option String
    | .lit (.strVal s) => some s
    | _ => none

/-- The union of atoms appearing in the hypotheses and the goal form. -/
def collectAtoms (hyps : Array Hyp) (g : LinComb) : MetaM (Array Expr) := do
  let mut atoms : Array Expr := #[]
  let push (atoms : Array Expr) (a : Expr) : MetaM (Array Expr) := do
    for b in atoms do
      if ← isDefEq a b then return atoms
    return atoms.push a
  for h in hyps do
    for (a, _) in h.p.coeffs do atoms ← push atoms a
  for (a, _) in g.coeffs do atoms ← push atoms a
  return atoms

/-- Coefficient of `atom` in `l`, comparing atoms up to `isDefEq`. -/
def LinComb.coeffOfM (l : LinComb) (atom : Expr) : MetaM Rat := do
  for (a, c) in l.coeffs do
    if ← isDefEq a atom then return c
  return 0

/-- Solve `Σ λⱼ · (column j) = target` over ℚ by Gaussian elimination, returning a
particular solution `λ` (free variables set to 0), or `none` if inconsistent.  `rows` is
the number of equations, `cols` the number of unknowns. -/
def gaussSolve (rows cols : Nat) (mat : Array (Array Rat)) (target : Array Rat) :
    Option (Array Rat) := Id.run do
  -- augmented matrix `aug`, `rows × (cols+1)`
  let mut aug := (Array.range rows).map (fun r => (mat[r]!).push (target[r]!))
  let mut pivotCol : Array Nat := #[]          -- pivotCol[k] = column of k-th pivot
  let mut pr := 0
  for c in [0:cols] do
    -- find a pivot row ≥ pr with nonzero entry in column c
    let mut piv := none
    for r in [pr:rows] do
      if aug[r]![c]! != 0 then piv := some r; break
    match piv with
    | none => pure ()
    | some r =>
      let tmp := aug[pr]!; aug := aug.set! pr aug[r]!; aug := aug.set! r tmp
      let lead := aug[pr]![c]!
      aug := aug.set! pr ((aug[pr]!).map (· / lead))
      for r2 in [0:rows] do
        if r2 != pr then
          let f := aug[r2]![c]!
          if f != 0 then
            aug := aug.set! r2 (Array.range (cols+1) |>.map
              (fun j => aug[r2]![j]! - f * aug[pr]![j]!))
      pivotCol := pivotCol.push c
      pr := pr + 1
  -- consistency: any all-zero-coefficient row with nonzero RHS ⇒ inconsistent
  for r in [0:rows] do
    let allZero := (Array.range cols).all (fun j => aug[r]![j]! == 0)
    if allZero && aug[r]![cols]! != 0 then return none
  -- read off the solution (free vars = 0)
  let mut sol := (Array.range cols).map (fun _ => (0 : Rat))
  for k in [0:pivotCol.size] do
    sol := sol.set! (pivotCol[k]!) (aug[k]![cols]!)
  return some sol

/-! ## The `llinarith` tactic

A proof-mode tactic.  Run inside a `by linear; lintro …` block whose context holds the
order resources.  Version 1 closes goals `e ≤ₐ f` whose certificate has coefficients in
`{0,1}` and no constant slack (transitivity / chaining / additive combinations); it folds
the chosen resources with `add_nonneg` and finishes through `le_congr`/`le_of_sub_nonneg`,
with the ring rearrangement discharged by `aring`. -/

/-- Affine `linarith` over an `AOrderedRing`, sequent-style: the order facts are resources
in the linear context.  See the module docstring. -/
elab "llinarith" : tactic => do
  let (ctx, G) ← Linear.getSeqGoal
  let (e, f) ← match G.getAppFnArgs with
    | (``AOrd.le, #[_, _, e, f]) => pure (e, f)
    | _ => throwError "llinarith: goal must be `e ≤ₐ f` (got `{G}`)"
  let carrierStx ← (← inferType e).toSyntax
  let g ← (← reflect f).add ((← reflect e).scale (-1))
  let (hyps, others) ← readHyps ctx
  let atoms ← collectAtoms hyps g
  let A := atoms.size
  let H := hyps.size
  -- Linear system `Σⱼ λⱼ · pⱼ = g` on the atoms only; the constant becomes the slack `s`,
  -- which is allowed to be any nonnegative value (one inequality, not an equation).
  let mut mat : Array (Array Rat) := #[]
  let mut target : Array Rat := #[]
  for i in [0:A] do
    let mut row : Array Rat := #[]
    for h in hyps do row := row.push (← h.p.coeffOfM atoms[i]!)
    mat := mat.push row
    target := target.push (← g.coeffOfM atoms[i]!)
  let some sol := gaussSolve A H mat target
    | throwError "llinarith: no nonnegative linear certificate"
  -- Coefficients must be nonnegative integers (the carrier has no division).
  for j in [0:H] do
    let c := sol[j]!
    unless c.den == 1 && c.num ≥ 0 do
      throwError "llinarith: coefficient {c} is not a nonnegative integer \
        (carrier has no division)"
  -- Constant slack `s = const(g) - Σⱼ λⱼ · const(pⱼ)` must itself be a nonnegative integer.
  let mut sConst := g.const
  for j in [0:H] do
    sConst := sConst - sol[j]! * hyps[j]!.p.const
  unless sConst.den == 1 && sConst.num ≥ 0 do
    throwError "llinarith: no nonnegative certificate (constant slack {sConst})"
  let sCount := sConst.num.toNat
  -- Scale each chosen `xⱼ ≤ₐ yⱼ` to `0 ≤ₐ (yⱼ + -xⱼ) * natMul λⱼ 1`; discard the rest.
  let mut foldNames : Array String := #[]
  for j in [0:H] do
    let nm := hyps[j]!.name
    let nmId := mkIdent (Name.mkSimple nm)
    let c := sol[j]!
    if c.num == 0 then
      evalTactic (← `(tactic| lweaken $nmId))
    else
      let cnt := Syntax.mkNatLit c.num.toNat
      let coeffId := mkIdent (Name.mkSimple s!"_llinc{j}")
      -- `0 ≤ₐ yⱼ + -xⱼ`, then scale by `natMul λⱼ 1` — the coefficient's nonnegativity
      -- enters as a resource (`lhave`) and is consumed by the sequent-style `mul_nonneg`.
      evalTactic (← `(tactic| lmap $nmId AOrderedRing.sub_nonneg_of_le))
      evalTactic (← `(tactic| lhave $coeffId
        (AOrderedRing.natMul_one_nonneg (α := $carrierStx) $cnt)))
      evalTactic (← `(tactic| lcombine $nmId $coeffId $nmId AOrderedRing.mul_nonneg))
      foldNames := foldNames.push nm
  for nm in others do
    evalTactic (← `(tactic| lweaken $(mkIdent (Name.mkSimple nm))))
  -- Inject the constant slack `0 ≤ₐ natMul s 1` as a resource.
  if sCount > 0 then
    let sLit := Syntax.mkNatLit sCount
    let sId := mkIdent (Name.mkSimple "_llinS")
    evalTactic (← `(tactic| lhave $sId
      (AOrderedRing.natMul_one_nonneg (α := $carrierStx) $sLit)))
    foldNames := foldNames.push "_llinS"
  if foldNames.isEmpty then
    -- The combination is identically `0`: `f + -e ≈ₐ 0`, so `e ≈ₐ f`, so `e ≤ₐ f`.
    evalTactic (← `(tactic| lexact (cut (by aring) AOrd.le_of_eq)))
  else
    -- Fold the chosen resources with `add_nonneg` into a single `0 ≤ₐ Σ`.
    let mut cur := foldNames[0]!
    for k in [1:foldNames.size] do
      let acc := s!"_llin{k}"
      let accId := mkIdent (Name.mkSimple acc)
      let curId := mkIdent (Name.mkSimple cur)
      let nxtId := mkIdent (Name.mkSimple foldNames[k]!)
      evalTactic (← `(tactic| lcombine $accId $curId $nxtId AOrderedRing.add_nonneg))
      cur := acc
    -- `0 ≤ₐ Σ`  ≈  `0 ≤ₐ f + -e`  ⊢  `e ≤ₐ f`; `simp` unfolds `natMul` for `aring`.
    evalTactic (← `(tactic|
      lexact (cut (AOrd.le_congr (by aring) (by simp only [natMul]; aring))
        AOrderedRing.le_of_sub_nonneg)))

end Linarith
end Antithesis
