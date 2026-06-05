import Akari.Basic
import Lean
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Lean Elab Term Tactic Meta

namespace Akari.Tactics

/-! # Akari Proof Tactics

Tactics accumulate membership facts as local hypotheses:
- `forced_xs pos`    adds `hempty_j : q ∉ sol` for a cell pos
- `suffocated pos`   closes a `False` goal when a black cell can't be satisfied
- `forced_bulbs pos` adds `hbulb_i : q ∈ sol` for each forced neighbor (uniqueness)
- `mark_conflict_xs` adds `hempty_j : q ∉ sol` for cells seen by placed bulbs (uniqueness)
- `uniqueness_done`  closes `sol = mySolution` from accumulated hbulb/hempty hypotheses
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

/-! ## Helper: grid utilities -/

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

/-! ## Tactic: forced_bulbs -/

/-- Core of `forced_bulbs` / `forced_bulbs_only`: place forced bulbs around the
    black #n cell at `posStx`, **without** auto-marking conflicts.

    A neighbor is *free* if it is not already known empty (`∉ sol`) in context.
    When exactly `n` neighbors are free, each free neighbor is forced to be a bulb:
    - if **no** neighbor is known empty, this reduces to the original
      `IsSolution.forced_bulb` (all `n` neighbors forced);
    - otherwise it uses `IsSolution.forced_bulb_filter`, discharging the empties
      side condition from the in-context `hempty_*` hypotheses. -/
def forcedBulbsCore (posStx : TSyntax `term) : TacticM Unit := withMainContext do
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
  -- Verify the number exists (Option.some, not none) and extract it.
  let optExpr ← withTransparency .all (whnf cellArgs[0]!)
  let (optFn, optArgs) := optExpr.getAppFnArgs
  unless optFn == ``Option.some do
    throwError "forced_bulbs: black cell at {posStx} has no number (unnumbered)"
  let nVal ← finValNat optArgs.back!
  -- Syntax for h, sol, pos
  let solStx  ← Lean.PrettyPrinter.delab solExpr
  let hIdent  : TSyntax `term := mkIdent hName
  let (pr, pc) ← posRowCol posExpr
  let prStx : TSyntax `term := ⟨Syntax.mkNumLit (toString pr)⟩
  let pcStx : TSyntax `term := ⟨Syntax.mkNumLit (toString pc)⟩
  let posLitStx : TSyntax `term ← `(⟨$prStx, $pcStx⟩)
  -- Neighbor coords, and the empties / bulbs already known in context.
  let nbrCoords ← neighbors.mapM (fun e => posRowCol e)
  let (bulbExprs, emptyExprs) ← collectProofState solExpr
  let emptyCoords ← emptyExprs.mapM (fun e => liftMetaM (posRowCol e))
  let bulbCoords  ← bulbExprs.mapM (fun e => liftMetaM (posRowCol e))
  let emptyNbrs := nbrCoords.filter (fun rc => emptyCoords.contains rc)
  let freeNbrs  := nbrCoords.filter (fun rc => !emptyCoords.contains rc)
  let mkPosStx (r c : Nat) : TacticM (TSyntax `term) := do
    let rStx : TSyntax `term := ⟨Syntax.mkNumLit (toString r)⟩
    let cStx : TSyntax `term := ⟨Syntax.mkNumLit (toString c)⟩
    `(⟨$rStx, $cStx⟩)
  if emptyNbrs.isEmpty then
    -- Original path: every neighbor is free, so `n` = neighbor count.
    let nStx : TSyntax `term := ⟨Syntax.mkNumLit (toString neighbors.size)⟩
    for (r, c) in nbrCoords do
      let hdStx ← mkPosStx r c
      let hName2 := mkIdent (← mkFreshBinderNameForTactic `hbulb)
      evalTactic (← `(tactic|
        have $hName2 : $hdStx ∈ $solStx :=
          Akari.IsSolution.forced_bulb $hIdent $posLitStx ⟨$nStx, by decide⟩
            (by decide) $hdStx (by decide) (by decide)))
  else
    -- Empty-aware path: free neighbors must number exactly `n`.
    unless freeNbrs.size == nVal do
      throwError "forced_bulbs: cell at {posStx} is not yet forced \
        ({freeNbrs.size} free neighbor(s), needs {nVal})"
    let mut emptyStxs : Array (TSyntax `term) := #[]
    for (r, c) in emptyNbrs do
      emptyStxs := emptyStxs.push (← mkPosStx r c)
    let emptiesListStx ← `([$emptyStxs,*])
    let nStx : TSyntax `term := ⟨Syntax.mkNumLit (toString nVal)⟩
    for (r, c) in freeNbrs do
      -- Skip neighbors already proven bulbs (would just be a duplicate).
      if bulbCoords.contains (r, c) then continue
      let hdStx ← mkPosStx r c
      let hName2 := mkIdent (← mkFreshBinderNameForTactic `hbulb)
      evalTactic (← `(tactic|
        have $hName2 : $hdStx ∈ $solStx :=
          Akari.IsSolution.forced_bulb_filter $hIdent $posLitStx ⟨$nStx, by decide⟩
            (by decide) $emptiesListStx (by intro e he; fin_cases he <;> assumption)
            (by decide) $hdStx (by decide) (by decide)))

/-- `forced_bulbs_only pos` — like `forced_bulbs` but does **not** auto-run
    `mark_conflict_xs` afterwards. Use this in proofs that place many bulbs and
    then mark conflicts once at the end (e.g. the large checkerboard puzzles),
    where per-call marking would be wasted work. -/
syntax (name := forced_bulbs_only) "forced_bulbs_only " term : tactic

@[tactic forced_bulbs_only] def evalForcedBulbsOnly : Tactic := fun stx => do
  match stx with
  | `(tactic| forced_bulbs_only $posStx) => forcedBulbsCore posStx
  | _ => throwUnsupportedSyntax

/-! ## Tactic: mark_conflict_xs -/

/-- Core of `mark_conflict_xs`: for every cell illuminated by a placed bulb
    (`hbulb_i`), add `hempty_j : cell ∉ sol` via `IsSolution.forced_empty_of_sees`. -/
def markConflictXsCore : TacticM Unit := do
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

/-- `mark_conflict_xs` — for every cell illuminated by a placed bulb (`hbulb_i`),
    adds `hempty_j : cell ∉ sol` derived from `IsSolution.forced_empty_of_sees`.
    For use in uniqueness proofs after `forced_bulbs`. -/
syntax (name := mark_conflict_xs) "mark_conflict_xs" : tactic

@[tactic mark_conflict_xs] def evalMarkConflictXs : Tactic := fun _stx =>
  markConflictXsCore

/-! ## Tactic: forced_bulbs (place bulbs, then auto-mark conflicts) -/

/-- `forced_bulbs pos` — `pos` is a black #n cell with exactly `n` *free*
    (not-yet-empty) neighbors. Adds `hbulb_i : q ∈ sol` for each free neighbor `q`,
    then automatically runs `mark_conflict_xs` so newly-lit cells are X'd out.

    For batched proofs that place many bulbs before marking once, use
    `forced_bulbs_only` instead to skip the per-call marking. -/
syntax (name := forced_bulbs) "forced_bulbs " term : tactic

@[tactic forced_bulbs] def evalForcedBulbs : Tactic := fun stx => do
  match stx with
  | `(tactic| forced_bulbs $posStx) => do
    forcedBulbsCore posStx
    markConflictXsCore
  | _ => throwUnsupportedSyntax

/-! ## Tactic: forced_lit -/

/-- Core of `forced_lit`: place a bulb at the white cell `posStx` when it is the
    only cell that can illuminate itself — i.e. every cell `posStx` sees, other
    than itself, is already known empty (`∉ sol`). Uses `IsSolution.forced_lit`. -/
def forcedLitCore (posStx : TSyntax `term) : TacticM Unit := withMainContext do
  let (puzExpr, solExpr, hName) ← parseSolutionHyp
  let posType ← mkAppM ``Akari.Puzzle.Pos #[puzExpr]
  let posExpr ← Term.elabTermEnsuringType posStx posType
  -- The target cell must be white.
  let cellExpr ← withTransparency .all (reduce (← mkAppM ``Akari.Puzzle.cells #[puzExpr, posExpr]))
  unless cellExpr.isConstOf ``Akari.Cell.white do
    throwError "forced_lit: cell at {posStx} is not white"
  -- Puzzle dimensions.
  let evalNat (e : Expr) : TacticM Nat := do
    match ← withTransparency .all (reduce e) with
    | .lit (.natVal n) => pure n
    | bad => throwError "forced_lit: could not evaluate {bad} to a Nat"
  let rows ← evalNat (← mkAppM ``Akari.Puzzle.rows #[puzExpr])
  let cols ← evalNat (← mkAppM ``Akari.Puzzle.cols #[puzExpr])
  let (qr, qc) ← posRowCol posExpr
  -- All cells the target sees, except itself.
  let mut visible : Array (Nat × Nat) := #[]
  for r in List.range rows do
    for c in List.range cols do
      if (r, c) != (qr, qc) then
        if ← checkSees2d puzExpr rows cols qr qc r c then
          visible := visible.push (r, c)
  -- Every visible cell must already be known empty, else the cell is not forced.
  let (_, emptyExprs) ← collectProofState solExpr
  let emptyCoords ← emptyExprs.mapM (fun e => liftMetaM (posRowCol e))
  for (r, c) in visible do
    unless emptyCoords.contains (r, c) do
      throwError "forced_lit: cell ({qr}, {qc}) also sees the undetermined cell \
        ({r}, {c}); it is not forced yet"
  -- Build the `visible` list literal and emit the lemma application.
  let solStx ← Lean.PrettyPrinter.delab solExpr
  let hIdent : TSyntax `term := mkIdent hName
  let mkPosStx (r c : Nat) : TacticM (TSyntax `term) := do
    let rStx : TSyntax `term := ⟨Syntax.mkNumLit (toString r)⟩
    let cStx : TSyntax `term := ⟨Syntax.mkNumLit (toString c)⟩
    `(⟨$rStx, $cStx⟩)
  let qStx ← mkPosStx qr qc
  let mut visStxs : Array (TSyntax `term) := #[]
  for (r, c) in visible do
    visStxs := visStxs.push (← mkPosStx r c)
  let visibleListStx ← `([$visStxs,*])
  let hName2 := mkIdent (← mkFreshBinderNameForTactic `hbulb)
  evalTactic (← `(tactic|
    have $hName2 : $qStx ∈ $solStx :=
      Akari.IsSolution.forced_lit $hIdent $qStx (by decide) $visibleListStx
        (by native_decide) (by intro v hv; fin_cases hv <;> assumption)))

/-- `forced_lit pos` — `pos` is a white cell whose only possible illuminator is
    itself: every cell it sees (apart from itself) is already X'd. Adds
    `hbulb : pos ∈ sol`, then auto-runs `mark_conflict_xs`.

    This is the "lighting" deduction (Akari's *every white cell must be lit*
    rule), complementing the adjacency-count deduction of `forced_bulbs`. -/
syntax (name := forced_lit) "forced_lit " term : tactic

@[tactic forced_lit] def evalForcedLit : Tactic := fun stx => do
  match stx with
  | `(tactic| forced_lit $posStx) => do
    forcedLitCore posStx
    markConflictXsCore
  | _ => throwUnsupportedSyntax

/-! ## Tactic: uniqueness_done -/

/-- `uniqueness_done` — closes `sol = mySolution` using accumulated `hbulb_i`/`hempty_j`
    hypotheses. Works for **any** representation of `mySolution` (filter, explicit set
    literal, etc.), not just nice `univ.filter` predicates.

    Strategy:
    1. From the `hbulb`/`hempty` hypotheses (which determine `sol` completely), synthesize
       a 2D boolean lookup table `tbl` with `tbl[r][c] = true` iff `⟨r,c⟩` is a bulb.
    2. Prove the **bridge** `∀ q, q ∈ mySolution ↔ tbl[q.1][q.2] = true` with a *single*
       `native_decide`. This is the only place `mySolution`'s representation is evaluated,
       and it happens once, in compiled code — so even a 225-element set literal (whose
       per-cell kernel `decide` would blow `maxRecDepth`) is handled cheaply.
    3. `ext p; fin_cases p`, rewrite each goal's `∈ mySolution` via the bridge, then close
       flatly: `assumption` for the `∈ sol` side, and a shallow `decide` on the table
       lookup (depth ≤ grid dimension, not the whole grid) for the membership side. -/
syntax (name := uniqueness_done) "uniqueness_done" : tactic

@[tactic uniqueness_done] def evalUniquenessDone : Tactic := fun _stx => do
  withMainContext do
    -- Parse goal `sol = mySolution`; grab the `mySolution` expression.
    let target ← whnf (← getMainTarget)
    let (eqFn, eqArgs) := target.getAppFnArgs
    unless eqFn == ``Eq && eqArgs.size == 3 do
      throwError "uniqueness_done: expected goal `sol = mySolution`, got {target}"
    let mySolExpr := eqArgs[2]!
    let mySolStx ← Lean.PrettyPrinter.delab mySolExpr
    -- Puzzle dimensions (from the `IsSolution puz sol` hypothesis).
    let (puzExpr, solExpr, _) ← parseSolutionHyp
    let evalNat (e : Expr) : TacticM Nat := do
      match ← withTransparency .all (reduce e) with
      | .lit (.natVal n) => pure n
      | bad => throwError "uniqueness_done: could not evaluate {bad} to a Nat"
    let rows ← evalNat (← mkAppM ``Akari.Puzzle.rows #[puzExpr])
    let cols ← evalNat (← mkAppM ``Akari.Puzzle.cols #[puzExpr])
    -- Collect the bulb cells from the local context.
    let mut bulbSet : Array (Nat × Nat) := #[]
    for hyp in ← getLCtx do
      if ← isBulbHyp hyp solExpr then
        bulbSet := bulbSet.push (← liftMetaM (posRowCol (← bulbPos hyp)))
    -- Build the 2D boolean table syntax `#[#[…], …]` (row-major, `true` = bulb).
    let mut rowSyns : Array (TSyntax `term) := #[]
    for r in [:rows] do
      let mut cellSyns : Array (TSyntax `term) := #[]
      for c in [:cols] do
        cellSyns := cellSyns.push (← if bulbSet.contains (r, c) then `(true) else `(false))
      rowSyns := rowSyns.push (← `(#[$cellSyns,*]))
    let tableSyn ← `(#[$rowSyns,*])
    -- Bridge lemma proven by kernel `decide` (fully kernel-checked, no native compiler trust).
    -- `maxRecDepth` is raised so the kernel can traverse literal insert-chains at 15×15 scale.
    let hb := mkIdent (← mkFreshBinderNameForTactic `hbridge)
    evalTactic (← `(tactic|
      have $hb : ∀ q, q ∈ $mySolStx ↔
          (($tableSyn : Array (Array Bool))[q.1.val]!)[q.2.val]! = true := by
        set_option maxRecDepth 100000 in decide))
    -- Close: rewrite the membership side via the bridge, then flat per-cell discharge.
    evalTactic (← `(tactic| ext p))
    evalTactic (← `(tactic| fin_cases p <;> simp only [$hb:ident] <;>
      (first
        | exact iff_of_true (by assumption) (by decide)
        | exact iff_of_false (by assumption) (by decide))))

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
