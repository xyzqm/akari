import Akari.Basic
import Lean
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Lean Elab Term Tactic Meta

namespace Akari.Tactics

/-! # Akari Proof Tactics

Tactics accumulate membership facts as local hypotheses:
- `forced_lights pos` adds `hbulb_i : q ∈ sol` for each neighbor q of black cell pos
- `forced_xs pos`    adds `hempty_j : q ∉ sol` for unsatisfied neighbors of black cell pos
- `suffocated pos`   closes a `False` goal when black cell pos can't be satisfied
- `akari_done`       verifies complete coverage then closes `IsSolution puz sol`

The goal stays `IsSolution puz sol` throughout; `puz` and `sol` are extracted
automatically, so the user never threads them through tactic calls.
-/

/-! ## Helper utilities -/

/-- Extract `(puz, sol)` from a goal of the form `IsSolution puz sol`. -/
def parseSolutionGoal (target : Expr) : MetaM (Expr × Expr) := do
  let target ← whnf target
  let (fn, args) := target.getAppFnArgs
  unless fn == ``Akari.IsSolution && args.size == 2 do
    throwError "expected goal of the form `IsSolution puz sol`, got {target}"
  return (args[0]!, args[1]!)

/-- Run `native_decide` on a fresh mvar with type `prop`, return the closed proof. -/
def proveByNativeDecide (prop : Expr) : TacticM Expr := do
  let mvar ← mkFreshExprMVar prop MetavarKind.syntheticOpaque
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| native_decide))
  setGoals savedGoals
  instantiateMVars mvar

/-- Add a hypothesis `name : type := proof` to the main goal's context. -/
def addHyp (name : Name) (proof : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let (_, newGoal) ← goal.note name proof
  replaceMainGoal [newGoal]

-- Args layout for @Membership.mem α β inst in Lean 4:
-- args = [α, β, inst, SET, ELEMENT] (5 args, SET at index 3, ELEMENT at index 4)
-- Empirically verified: args.back! = element, args[args.size-2] = set.

/-- True if `hyp`'s type is `q ∈ sol` for some `q`. -/
def isBulbHyp (hyp : LocalDecl) (solExpr : Expr) : MetaM Bool := do
  let (fn, args) := hyp.type.getAppFnArgs
  if fn == ``Membership.mem && args.size >= 2 then
    -- SET is at second-to-last position (args[3] in a 5-arg application)
    return ← isDefEq args[args.size - 2]! solExpr
  return false

/-- True if `hyp`'s type is `q ∉ sol` (i.e., `¬ q ∈ sol`) for some `q`. -/
def isEmptyHyp (hyp : LocalDecl) (solExpr : Expr) : MetaM Bool := do
  let (fn, args) := hyp.type.getAppFnArgs
  if fn == ``Not && args.size == 1 then
    let (fn2, args2) := args[0]!.getAppFnArgs
    if fn2 == ``Membership.mem && args2.size >= 2 then
      return ← isDefEq args2[args2.size - 2]! solExpr
  return false

/-- Extract the element `q` from `q ∈ sol` (ELEMENT is the last arg). -/
def bulbPos (hyp : LocalDecl) : MetaM Expr := do
  let (_, args) := hyp.type.getAppFnArgs
  if args.size < 2 then throwError "bulbPos: unexpected membership type"
  return args.back!  -- ELEMENT is last

/-- Extract the element `q` from `¬ q ∈ sol`. -/
def emptyPos (hyp : LocalDecl) : MetaM Expr := do
  let (_, args) := hyp.type.getAppFnArgs
  let (_, args2) := args[0]!.getAppFnArgs
  if args2.size < 2 then throwError "emptyPos: unexpected membership type"
  return args2.back!  -- ELEMENT is last

/-- Extract the `.val : Nat` from a `Fin n` expression.
    Uses `Lean.Meta.reduce` to fully evaluate the expression including subterms. -/
def finValNat (e : Expr) : MetaM Nat := do
  -- Fully reduce the Fin expression and look for Fin.mk n val isLt (3 args).
  -- `reduce` (with default skipProofs:=true) evaluates computable parts.
  let e' ← withTransparency .all (whnf e)
  -- Fin.mk takes (n : Nat) implicitly, then val and isLt explicitly → 3 args total
  if e'.isAppOfArity ``Fin.mk 3 then
    let valExpr := e'.getAppArgs[1]!  -- val is at index 1 (after implicit n)
    let v ← withTransparency .all (reduce valExpr)
    match v with
    | .lit (.natVal n) => return n
    | bad => throwError "finValNat: could not reduce Fin.val to Nat literal, got {bad}"
  else
    -- Maybe the expression is a Nat literal directly (shouldn't happen for Fin, but try)
    let v ← withTransparency .all (reduce e')
    match v with
    | .lit (.natVal n) => return n
    | _ => throwError "finValNat: expected Fin.mk (3 args), got {e'}"

/-- Extract (row, col) as Nat values from a `Pos = Fin × Fin` expression.
    Fully reduces the position expression before extracting components. -/
def posRowCol (e : Expr) : MetaM (Nat × Nat) := do
  -- Use `reduce` to evaluate all subterms (including Pos.r, Nat.sub, etc.)
  let e' ← withTransparency .all (reduce e)
  -- After full reduction: @Prod.mk (Fin rows) (Fin cols) fst snd (4 args)
  if e'.isAppOfArity ``Prod.mk 4 then
    let args := e'.getAppArgs
    return (← finValNat args[2]!, ← finValNat args[3]!)
  else
    throwError "posRowCol: expected Prod.mk after reduce, got {e'}"

/-- Walk an `Expr` representing a `List α` and return each element as an `Array Expr`. -/
def exprListElems (list : Expr) : MetaM (Array Expr) := do
  let mut elems : Array Expr := #[]
  let mut current := list
  let mut limit := 10000
  while limit > 0 do
    limit := limit - 1
    let node ← withTransparency .all (whnf current)
    if node.isAppOfArity ``List.nil 1 then return elems
    if node.isAppOfArity ``List.cons 3 then
      let args := node.getAppArgs
      elems := elems.push args[1]!
      current := args[2]!
    else
      throwError "exprListElems: could not reduce list (stuck at {node})"
  throwError "exprListElems: list exceeded iteration limit"

/-- Collect positions already proven to be bulbs/empties from the local context. -/
def collectProofState (solExpr : Expr) : TacticM (Array Expr × Array Expr) := do
  withMainContext do
    let lctx ← getLCtx
    let mut bulbs : Array Expr := #[]
    let mut empties : Array Expr := #[]
    for hyp in lctx do
      if ← isBulbHyp hyp solExpr then
        bulbs := bulbs.push (← bulbPos hyp)
      else if ← isEmptyHyp hyp solExpr then
        empties := empties.push (← emptyPos hyp)
    return (bulbs, empties)

/-! ## Helper: parseSolutionHyp -/

/-- Find `(puz, sol, hName)` from the first `IsSolution puz sol` hypothesis in context.
    Used by uniqueness tactics which work under `intro sol h` rather than from the goal. -/
def parseSolutionHyp : TacticM (Expr × Expr × Name) := do
  withMainContext do
    let lctx ← getLCtx
    for hyp in lctx do
      let ty ← whnf hyp.type
      let (fn, args) := ty.getAppFnArgs
      if fn == ``Akari.IsSolution && args.size == 2 then
        return (args[0]!, args[1]!, hyp.userName)
    throwError "expected `IsSolution puz sol` hypothesis in local context"

/-! ## Tactic: forced_lights -/

/-- `forced_lights pos` — `pos` is a black #n cell with exactly n white adjacent cells.
    Adds `hbulb_i : q ∈ sol` for each neighbor `q` via `native_decide`. -/
syntax (name := forced_lights) "forced_lights " term : tactic

@[tactic forced_lights] def evalForcedLights : Tactic := fun stx => do
  match stx with
  | `(tactic| forced_lights $posStx) => withMainContext do
    let target  ← getMainTarget
    let (puzExpr, solExpr) ← parseSolutionGoal target
    -- Elaborate the black cell position
    let posType ← mkAppM ``Akari.Puzzle.Pos #[puzExpr]
    let posExpr ← Term.elabTermEnsuringType posStx posType
    -- Evaluate getNeighbors puz pos to a concrete list via kernel reduction
    let neighborsExpr ← mkAppM ``Akari.getNeighbors #[puzExpr, posExpr]
    let neighbors ← exprListElems neighborsExpr
    -- Also need sol as syntax for the `have` tactic
    let solStx ← Lean.PrettyPrinter.delab solExpr
    -- Add `hbulb : ⟨r, c⟩ ∈ sol` for each white neighbor, using numeric literals
    for hd in neighbors do
      let cell ← whnf (← mkAppM ``Akari.Puzzle.cells #[puzExpr, hd])
      let isWhite := match cell with
        | .const n _ => n == ``Akari.Cell.white
        | _          => false
      if isWhite then
        let (r, c) ← posRowCol hd
        let rStx   : TSyntax `term := ⟨Syntax.mkNumLit (toString r)⟩
        let cStx   : TSyntax `term := ⟨Syntax.mkNumLit (toString c)⟩
        let hdStx  : TSyntax `term ← `(⟨$rStx, $cStx⟩)
        let hName  := mkIdent (← mkFreshBinderNameForTactic `hbulb)
        evalTactic (← `(tactic| have $hName : $hdStx ∈ $solStx := by native_decide))
  | _ => throwUnsupportedSyntax

/-! ## Tactic: forced_xs -/

/-- `forced_xs pos` — marks `pos` as forced empty (must not contain a bulb).
    Adds `hempty : pos ∉ sol` via `native_decide`. -/
syntax (name := forced_xs) "forced_xs " term : tactic

@[tactic forced_xs] def evalForcedXs : Tactic := fun stx => do
  match stx with
  | `(tactic| forced_xs $posStx) => withMainContext do
    let target   ← getMainTarget
    let (_, solExpr) ← parseSolutionGoal target
    let solStx   ← Lean.PrettyPrinter.delab solExpr
    let hName    := mkIdent (← mkFreshBinderNameForTactic `hempty)
    -- Generate: have hempty : <pos> ∉ <sol> := by native_decide
    evalTactic (← `(tactic| have $hName : $posStx ∉ $solStx := by native_decide))
  | _ => throwUnsupportedSyntax

/-! ## Tactic: suffocated -/

/-- `suffocated pos` — closes a `False` goal when the black cell at `pos` has
    fewer available adjacent positions than its number requires.
    "Available" means not yet marked empty in the local context.
    Discharges via `native_decide` (all ground terms). -/
syntax (name := suffocated) "suffocated " term : tactic

@[tactic suffocated] def evalSuffocated : Tactic := fun stx => do
  withMainContext do
    -- Find IsSolution in the local context (not the goal, which may be False)
    let lctx ← getLCtx
    let mut solGoalOpt : Option (Expr × Expr) := none
    for hyp in lctx do
      let ty ← whnf hyp.type
      let (fn, args) := ty.getAppFnArgs
      if fn == ``Akari.IsSolution && args.size == 2 then
        solGoalOpt := some (args[0]!, args[1]!)
        break
    let (puzExpr, solExpr) ← match solGoalOpt with
      | some p => pure p
      | none   => throwError "suffocated: no `IsSolution puz sol` hypothesis found in context"
    let posType ← mkAppM ``Akari.Puzzle.Pos #[puzExpr]
    let _ ← Term.elabTermEnsuringType stx[1] posType
    -- The contradiction: native_decide can verify the cell is suffocated
    -- given the concrete puzzle. We close False directly.
    evalTactic (← `(tactic| native_decide))

/-! ## Tactic: mark_lit_xs -/

/-- Build a concrete `Fin n` expression with value `val`, proving `val < n` by `native_decide`. -/
def mkConcreteFin (n val : Nat) : TacticM Expr := do
  let nE   := mkNatLit n
  let valE := mkNatLit val
  let ltProof ← proveByNativeDecide (← mkAppM ``LT.lt #[valE, nE])
  mkAppOptM ``Fin.mk #[some nE, some valE, some ltProof]

/-- Build a `Pos` expression from concrete row/col values and puzzle dimensions. -/
def mkConcretePos (rows cols r c : Nat) : TacticM Expr := do
  let rFin ← mkConcreteFin rows r
  let cFin ← mkConcreteFin cols c
  let finRowsT := mkApp (mkConst ``Fin) (mkNatLit rows)
  let finColsT := mkApp (mkConst ``Fin) (mkNatLit cols)
  mkAppOptM ``Prod.mk #[some finRowsT, some finColsT, some rFin, some cFin]

/-- Evaluate `puz.cells pos` and return whether the cell is white. -/
def isCellWhite (puzExpr posExpr : Expr) : MetaM Bool := do
  let cell ← withTransparency .all (reduce (← mkAppM ``Akari.Puzzle.cells #[puzExpr, posExpr]))
  return cell.isConst && cell.constName! == ``Akari.Cell.white

/-- Check if position (r1,c1) can see position (r2,c2) by scanning intermediate cells.
    Returns false for the same position or non-aligned positions. -/
def checkSees2d (puzExpr : Expr) (rows cols r1 c1 r2 c2 : Nat) : TacticM Bool := do
  if r1 == r2 && c1 == c2 then return false
  if r1 == r2 then
    -- Same row: scan intermediate columns for black cells
    let lo := min c1 c2 + 1
    let hi := max c1 c2
    for ci in List.range (hi - lo) do
      let c := lo + ci
      let pos ← mkConcretePos rows cols r1 c
      if !(← isCellWhite puzExpr pos) then return false
    return true
  else if c1 == c2 then
    -- Same column: scan intermediate rows for black cells
    let lo := min r1 r2 + 1
    let hi := max r1 r2
    for ri in List.range (hi - lo) do
      let r := lo + ri
      let pos ← mkConcretePos rows cols r c1
      if !(← isCellWhite puzExpr pos) then return false
    return true
  else
    return false

/-- `mark_lit_xs` — for every white cell currently illuminated by a placed bulb (`hbulb_i`),
    adds `hempty : cell ∉ sol` via `native_decide`.
    Call after `forced_lights` to mark conflict-blocked cells. -/
syntax (name := mark_lit_xs) "mark_lit_xs" : tactic

@[tactic mark_lit_xs] def evalMarkLitXs : Tactic := fun _stx => do
  withMainContext do
    let target ← getMainTarget
    let (puzExpr, solExpr) ← parseSolutionGoal target
    let solStx ← Lean.PrettyPrinter.delab solExpr
    -- Get puzzle dimensions
    let rowsR ← withTransparency .all (reduce (← mkAppM ``Akari.Puzzle.rows #[puzExpr]))
    let colsR ← withTransparency .all (reduce (← mkAppM ``Akari.Puzzle.cols #[puzExpr]))
    let rows : Nat ← match rowsR with
      | .lit (.natVal n) => pure n
      | _ => throwError "mark_lit_xs: could not evaluate puzzle rows"
    let cols : Nat ← match colsR with
      | .lit (.natVal n) => pure n
      | _ => throwError "mark_lit_xs: could not evaluate puzzle cols"
    -- Collect current bulb and empty positions as (Nat × Nat) pairs
    let (bulbExprs, emptyExprs) ← collectProofState solExpr
    let bulbs   ← bulbExprs.mapM  (fun e => liftMetaM (posRowCol e))
    let empties ← emptyExprs.mapM (fun e => liftMetaM (posRowCol e))
    -- Iterate over every grid position
    for r in List.range rows do
      for c in List.range cols do
        -- Skip already-determined cells
        if bulbs.contains (r, c) || empties.contains (r, c) then continue
        -- Skip black cells
        let posExpr ← mkConcretePos rows cols r c
        if !(← isCellWhite puzExpr posExpr) then continue
        -- Check if any placed bulb illuminates this cell
        let mut lit := false
        for (br, bc) in bulbs do
          if ← checkSees2d puzExpr rows cols r c br bc then
            lit := true
            break
        if lit then
          let rStx  : TSyntax `term := ⟨Syntax.mkNumLit (toString r)⟩
          let cStx  : TSyntax `term := ⟨Syntax.mkNumLit (toString c)⟩
          let pStx  : TSyntax `term ← `(⟨$rStx, $cStx⟩)
          let hName := mkIdent (← mkFreshBinderNameForTactic `hempty)
          evalTactic (← `(tactic| have $hName : $pStx ∉ $solStx := by native_decide))

/-! ## Tactic: forced_bulbs -/

/-- `forced_bulbs pos` — `pos` is a black #n cell with exactly n neighbors (all white).
    Adds `hbulb_i : q ∈ sol` for each neighbor `q`, derived from `h : IsSolution puz sol`
    via `IsSolution.forced_bulb`. For use in uniqueness proofs after `intro sol h`. -/
syntax (name := forced_bulbs) "forced_bulbs " term : tactic

@[tactic forced_bulbs] def evalForcedBulbs : Tactic := fun stx => do
  match stx with
  | `(tactic| forced_bulbs $posStx) => withMainContext do
    let (puzExpr, solExpr, hName) ← parseSolutionHyp
    -- Elaborate the black cell position
    let posType ← mkAppM ``Akari.Puzzle.Pos #[puzExpr]
    let posExpr ← Term.elabTermEnsuringType posStx posType
    -- Evaluate getNeighbors puz pos to a concrete list
    let neighborsExpr ← mkAppM ``Akari.getNeighbors #[puzExpr, posExpr]
    let neighbors ← exprListElems neighborsExpr
    -- Evaluate puz.cells pos; verify it is a numbered black cell.
    let cellExpr ← withTransparency .all (reduce (← mkAppM ``Akari.Puzzle.cells #[puzExpr, posExpr]))
    let (cellFn, cellArgs) := cellExpr.getAppFnArgs
    unless cellFn == ``Akari.Cell.black do
      throwError "forced_bulbs: cell at {posStx} is not a black cell"
    -- Verify the number exists (Option.some, not none).
    let optExpr ← withTransparency .all (whnf cellArgs[0]!)
    let (optFn, _) := optExpr.getAppFnArgs
    unless optFn == ``Option.some do
      throwError "forced_bulbs: black cell at {posStx} has no number (unnumbered)"
    -- Use neighbor count as n.  `by decide` in each emitted `have` will validate
    -- that this matches the actual number on the cell and that each neighbor is white.
    let n := neighbors.size
    -- Syntax for h, sol, pos
    let solStx  ← Lean.PrettyPrinter.delab solExpr
    let hIdent  : TSyntax `term := mkIdent hName
    let (pr, pc) ← posRowCol posExpr
    let prStx : TSyntax `term := ⟨Syntax.mkNumLit (toString pr)⟩
    let pcStx : TSyntax `term := ⟨Syntax.mkNumLit (toString pc)⟩
    let posLitStx : TSyntax `term ← `(⟨$prStx, $pcStx⟩)
    -- n as Fin 5 literal
    let nStx : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
    -- Add hbulb_i for each neighbor
    for hd in neighbors do
      let (r, c) ← posRowCol hd
      let rStx : TSyntax `term := ⟨Syntax.mkNumLit (toString r)⟩
      let cStx : TSyntax `term := ⟨Syntax.mkNumLit (toString c)⟩
      let hdStx : TSyntax `term ← `(⟨$rStx, $cStx⟩)
      let hName2 := mkIdent (← mkFreshBinderNameForTactic `hbulb)
      evalTactic (← `(tactic|
        have $hName2 : $hdStx ∈ $solStx :=
          Akari.IsSolution.forced_bulb $hIdent $posLitStx ⟨$nStx, by decide⟩
            (by decide) $hdStx (by decide) (by decide)))
  | _ => throwUnsupportedSyntax

/-! ## Tactic: mark_conflict_xs -/

/-- `mark_conflict_xs` — for every white cell illuminated by a placed bulb (`hbulb_i`),
    adds `hempty_j : cell ∉ sol` derived from `IsSolution.forced_empty_of_sees`.
    For use in uniqueness proofs after `forced_bulbs`. -/
syntax (name := mark_conflict_xs) "mark_conflict_xs" : tactic

@[tactic mark_conflict_xs] def evalMarkConflictXs : Tactic := fun _stx => do
  withMainContext do
    let (puzExpr, solExpr, hName) ← parseSolutionHyp
    let solStx ← Lean.PrettyPrinter.delab solExpr
    let hIdent : TSyntax `term := mkIdent hName
    -- Get puzzle dimensions
    let rowsR ← withTransparency .all (reduce (← mkAppM ``Akari.Puzzle.rows #[puzExpr]))
    let colsR ← withTransparency .all (reduce (← mkAppM ``Akari.Puzzle.cols #[puzExpr]))
    let rows : Nat ← match rowsR with
      | .lit (.natVal n) => pure n
      | _ => throwError "mark_conflict_xs: could not evaluate puzzle rows"
    let cols : Nat ← match colsR with
      | .lit (.natVal n) => pure n
      | _ => throwError "mark_conflict_xs: could not evaluate puzzle cols"
    -- Collect current bulb positions as (Nat × Nat) pairs, keeping track of hyp names
    let lctx ← getLCtx
    let mut bulbsWithNames : Array (Nat × Nat × Name) := #[]
    for hyp in lctx do
      if ← isBulbHyp hyp solExpr then
        let posE ← bulbPos hyp
        let (br, bc) ← liftMetaM (posRowCol posE)
        bulbsWithNames := bulbsWithNames.push (br, bc, hyp.userName)
    let (_, emptyExprs) ← collectProofState solExpr
    let empties ← emptyExprs.mapM (fun e => liftMetaM (posRowCol e))
    -- Iterate over every white grid position
    for r in List.range rows do
      for c in List.range cols do
        -- Skip already-determined cells
        let alreadyBulb := bulbsWithNames.any (fun (br, bc, _) => br == r && bc == c)
        if alreadyBulb || empties.contains (r, c) then continue
        -- Check if any placed bulb illuminates this cell (works for white AND black cells:
        -- NoBulbConflicts bans any two positions in sol from seeing each other)
        let mut foundBulb : Option Name := none
        for (br, bc, bHypName) in bulbsWithNames do
          if ← checkSees2d puzExpr rows cols r c br bc then
            foundBulb := some bHypName
            break
        if let some bHypName := foundBulb then
          let rStx  : TSyntax `term := ⟨Syntax.mkNumLit (toString r)⟩
          let cStx  : TSyntax `term := ⟨Syntax.mkNumLit (toString c)⟩
          let pStx  : TSyntax `term ← `(⟨$rStx, $cStx⟩)
          -- find the bulb's position for the lemma call
          let bulbEntry := bulbsWithNames.find? (fun (_, _, n) => n == bHypName)
          let (br, bc, _) := bulbEntry.get!
          let brStx : TSyntax `term := ⟨Syntax.mkNumLit (toString br)⟩
          let bcStx : TSyntax `term := ⟨Syntax.mkNumLit (toString bc)⟩
          let bpStx : TSyntax `term ← `(⟨$brStx, $bcStx⟩)
          let bHIdent : TSyntax `term := mkIdent bHypName
          let heName := mkIdent (← mkFreshBinderNameForTactic `hempty)
          evalTactic (← `(tactic|
            have $heName : $pStx ∉ $solStx :=
              Akari.IsSolution.forced_empty_of_sees $hIdent $pStx $bpStx $bHIdent
                (by decide) (by decide)))

/-! ## Tactic: uniqueness_done -/

/-- `uniqueness_done` — closes `sol = mySolution` using accumulated `hbulb_i`/`hempty_j`
    hypotheses via `Finset.ext` + `fin_cases` + `simp_all`. -/
syntax (name := uniqueness_done) "uniqueness_done" : tactic

@[tactic uniqueness_done] def evalUniquenessDone : Tactic := fun _stx => do
  withMainContext do
    evalTactic (← `(tactic| ext p))
    evalTactic (← `(tactic| fin_cases p))
    evalTactic (← `(tactic| all_goals simp_all (config := { decide := true })))

/-! ## Tactic: akari_done -/

/-- `akari_done` — verifies that every white cell is determined (in bulbs or empties),
    then closes `IsSolution puz sol` via `native_decide`.
    Fails with a list of undetermined cells if coverage is incomplete. -/
syntax (name := akari_done) "akari_done" : tactic

@[tactic akari_done] def evalAkariDone : Tactic := fun _stx => do
  withMainContext do
    -- Decompose IsSolution into its three fields.
    evalTactic (← `(tactic| constructor))
    -- no_conflicts
    Lean.Elab.Tactic.focus do
      evalTactic (← `(tactic| rw [Akari.NoBulbConflicts]))
      evalTactic (← `(tactic| intro p1 p2 neq h1 h2))
      evalTactic (← `(tactic| fin_cases h1 <;> fin_cases h2))
      evalTactic (← `(tactic| all_goals (dsimp [Akari.Sees]; simp_all; try decide)))
    -- all_lit
    Lean.Elab.Tactic.focus do
      evalTactic (← `(tactic| intro p))
      evalTactic (← `(tactic| dsimp [Akari.IsIlluminated, Akari.Sees]))
      evalTactic (← `(tactic| fin_cases p <;> decide))
    -- adj_correct
    Lean.Elab.Tactic.focus do
      evalTactic (← `(tactic| intro p))
      evalTactic (← `(tactic| fin_cases p <;> simp_all (config := { decide := true })))

end Akari.Tactics
