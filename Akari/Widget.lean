import Akari.Basic
import Akari.Tactics.Basic
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.Panel.Basic

open Lean Elab Tactic Meta Server
open ProofWidgets (Html Component PanelWidgetProps)
open Akari.Tactics

namespace Akari

/-! ## Akari proof-state visualisation

**Auto-updating widget** — activate once, then move the cursor freely:
```lean
theorem proof : ∀ sol, IsSolution puz sol → sol = mySol := by
  intro sol h
  with_panel_widgets [AkariPanelWidget]
    forced_bulbs ⟨1, 1⟩   -- cursor here → grid shows 4 bulbs placed
    mark_conflict_xs        -- cursor here → all cells marked ✗
    uniqueness_done
```

Or use the `show_puzzle` shorthand (wraps the same block):
```lean
  intro sol h
  show_puzzle
    forced_bulbs ⟨1, 1⟩
    mark_conflict_xs
    uniqueness_done
```

Cell colours
  ■ dark   = black cell (digit shown in white)
  □ white  = undecided white cell
  ● yellow = confirmed bulb   (hbulb_* hypothesis)
  ✗ grey   = confirmed empty  (hempty_* hypothesis)
-/

-- ════════════════════════════════════════════════════════════════════════════
-- § Style helper
--   React requires CSS as a JS object {alignItems:"center"}, NOT a string.
-- ════════════════════════════════════════════════════════════════════════════

private def styleAttr (kvs : List (String × String)) : String × Json :=
  ("style", Json.mkObj (kvs.map fun (k, v) => (k, .str v)))

-- ════════════════════════════════════════════════════════════════════════════
-- § MetaM helpers (no TacticM needed; safe to call from the RPC method)
-- ════════════════════════════════════════════════════════════════════════════

/-- Prove `val < n` for concrete `Nat` literals by synthesising the `Decidable`
    instance and reducing it to `isTrue proof`. -/
private def mkBoundProofM (n val : Nat) : MetaM Expr := do
  let p    ← mkAppM ``LT.lt #[mkNatLit val, mkNatLit n]
  let inst ← synthInstance (← mkAppM ``Decidable #[p])
  let r    ← withTransparency .all (reduce inst)
  if r.isAppOfArity ``Decidable.isTrue 2 then return r.getAppArgs[1]!
  throwError "mkBoundProofM: {val} ≮ {n}"

/-- Build `⟨Fin.mk rows r _, Fin.mk cols c _⟩` as an `Expr` in MetaM. -/
private def mkConcretePosM (rows cols r c : Nat) : MetaM Expr := do
  let rProof ← mkBoundProofM rows r
  let cProof ← mkBoundProofM cols c
  let rFin ← mkAppOptM ``Fin.mk
    #[some (mkNatLit rows), some (mkNatLit r), some rProof]
  let cFin ← mkAppOptM ``Fin.mk
    #[some (mkNatLit cols), some (mkNatLit c), some cProof]
  mkAppOptM ``Prod.mk
    #[some (mkApp (mkConst ``Fin) (mkNatLit rows)),
      some (mkApp (mkConst ``Fin) (mkNatLit cols)),
      some rFin, some cFin]

/-- Evaluate `puz.cells ⟨r, c⟩` and return `(isWhite, numberLabel?)`. -/
private def getCellKindM (puzExpr : Expr) (rows cols r c : Nat) :
    MetaM (Bool × Option Nat) := do
  let pos  ← mkConcretePosM rows cols r c
  let cell ← withTransparency .all
    (reduce (← mkAppM ``Akari.Puzzle.cells #[puzExpr, pos]))
  let (fn, args) := cell.getAppFnArgs
  if fn == ``Akari.Cell.white then return (true, none)
  else if fn == ``Akari.Cell.black && !args.isEmpty then
    let opt ← withTransparency .all (whnf args[0]!)
    let (optFn, optArgs) := opt.getAppFnArgs
    if optFn == ``Option.some && !optArgs.isEmpty then
      let n ← finValNat optArgs.back!
      return (false, some n)
    else return (false, none)
  else return (true, none)

/-- Collect all `hbulb_*` / `hempty_*` positions from `lctx`. -/
private def collectStateM (solExpr : Expr) (lctx : LocalContext) :
    MetaM (Array (Nat × Nat) × Array (Nat × Nat)) := do
  let mut bulbs   : Array (Nat × Nat) := #[]
  let mut empties : Array (Nat × Nat) := #[]
  for hyp in lctx do
    if ← isBulbHyp hyp solExpr then
      bulbs := bulbs.push (← posRowCol (← bulbPos hyp))
    else if ← isEmptyHyp hyp solExpr then
      empties := empties.push (← posRowCol (← emptyPos hyp))
  return (bulbs, empties)

/-- Try to locate `(puz, sol)` — first in the goal type, then in hypotheses. -/
private def findPuzSolM (goalType : Expr) (lctx : LocalContext) :
    MetaM (Expr × Expr) := do
  match ← try pure (some (← parseSolutionGoal goalType)) catch _ => pure none with
  | some ps => return ps
  | none =>
    for hyp in lctx do
      let ty ← whnf hyp.type
      let (fn, args) := ty.getAppFnArgs
      if fn == ``Akari.IsSolution && args.size == 2 then
        return (args[0]!, args[1]!)
    throwError "no IsSolution in goal or context"

-- ════════════════════════════════════════════════════════════════════════════
-- § HTML grid renderer (MetaM)
-- ════════════════════════════════════════════════════════════════════════════

private def puzzleHtmlM (puzExpr : Expr) (rows cols : Nat)
    (bulbs empties : Array (Nat × Nat)) : MetaM Html := do
  let sz  := 44
  let gap := 3
  let mut cells : Array Html := #[]
  for r in List.range rows do
    for c in List.range cols do
      let (isWhite, numOpt) ← getCellKindM puzExpr rows cols r c
      let isBulb  := bulbs.contains (r, c)
      let isEmpty := empties.contains (r, c)
      let bg : String :=
        if !isWhite then "#2a2a2a"
        else if isBulb  then "#fffacd"
        else if isEmpty then "#e0e0e0"
        else "#ffffff"
      let (text, color) : String × String :=
        if !isWhite then (numOpt.map toString |>.getD "", "#ffffff")
        else if isBulb  then ("●", "#c07800")
        else if isEmpty then ("✗", "#999")
        else ("", "#000")
      cells := cells.push <| Html.element "div"
        #[styleAttr [
            ("display", "flex"), ("alignItems", "center"),
            ("justifyContent", "center"),
            ("fontSize", s!"{sz * 55 / 100}px"),
            ("background", bg), ("color", color),
            ("borderRadius", "2px"), ("fontFamily", "sans-serif"),
            ("userSelect", "none")]]
        #[.text text]
  return Html.element "div"
    #[styleAttr [("display", "inline-block"), ("padding", "8px")]]
    #[Html.element "div"
        #[styleAttr [
            ("display", "inline-grid"),
            ("gridTemplateColumns", s!"repeat({cols},{sz}px)"),
            ("gridTemplateRows",    s!"repeat({rows},{sz}px)"),
            ("gap", s!"{gap}px"), ("background", "#666"),
            ("padding", s!"{gap}px"), ("borderRadius", "4px")]]
        cells,
      Html.element "p"
        #[styleAttr [("margin", "4px 0 0"), ("fontSize", "11px"),
                     ("color", "#555"), ("fontFamily", "sans-serif")]]
        #[.text s!"● bulb ({bulbs.size}) · ✗ empty ({empties.size})"]]

-- ════════════════════════════════════════════════════════════════════════════
-- § RPC method + widget module
-- ════════════════════════════════════════════════════════════════════════════

private def noAkariHtml : Html :=
  Html.element "p"
    #[styleAttr [("color", "#888"), ("fontSize", "12px"),
                 ("fontFamily", "sans-serif"), ("padding", "8px")]]
    #[.text "Place cursor inside an Akari proof."]

/-- RPC method.  The infoview calls this on every cursor move; it reads the
    current goal's local context, locates the Akari puzzle, and returns
    the up-to-date grid HTML. -/
@[server_rpc_method]
def AkariPanelWidget.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    -- No goals means the proof is finished.
    let some goal := props.goals[0]? | return noAkariHtml
    -- Run inside the goal's elaboration context (env + mctx).
    goal.ctx.val.runMetaM {} do
    -- Bring the goal's local context into scope.
    let mvarDecl := (← getMCtx).getDecl goal.mvarId
    withLCtx mvarDecl.lctx mvarDecl.localInstances do
    let lctx     ← getLCtx
    let goalType := mvarDecl.type
    -- Attempt to render the puzzle; silently return placeholder on failure.
    let htmlOpt : Option Html ← do
      try
        let (puzExpr, solExpr) ← findPuzSolM goalType lctx
        let rowsE ← withTransparency .all
          (reduce (← mkAppM ``Akari.Puzzle.rows #[puzExpr]))
        let colsE ← withTransparency .all
          (reduce (← mkAppM ``Akari.Puzzle.cols #[puzExpr]))
        let rows ← match rowsE with
          | .lit (.natVal n) => pure n
          | _ => throwError "rows"
        let cols ← match colsE with
          | .lit (.natVal n) => pure n
          | _ => throwError "cols"
        let (bulbs, empties) ← collectStateM solExpr lctx
        let html ← puzzleHtmlM puzExpr rows cols bulbs empties
        pure (some html)
      catch _ => pure none
    return htmlOpt.getD noAkariHtml

/-- Panel widget.  Activate with `with_panel_widgets [AkariPanelWidget]`. -/
@[widget_module]
def AkariPanelWidget : Component PanelWidgetProps :=
  mk_rpc_widget% AkariPanelWidget.rpc

-- ════════════════════════════════════════════════════════════════════════════
-- § `show_puzzle` tactic
-- ════════════════════════════════════════════════════════════════════════════

/-- `show_puzzle` — display the Akari grid in the Lean infoview at the current
    proof step.  Place the cursor on the `show_puzzle` line to see the grid
    (bulbs ●, empties ✗, unknowns □) for the proof state at that point.

    For an auto-updating view that follows the cursor through the whole proof,
    use `with_panel_widgets [AkariPanelWidget]` around the tactic block instead:
    ```lean
    with_panel_widgets [AkariPanelWidget]
      forced_bulbs ⟨1, 1⟩
      mark_conflict_xs
      uniqueness_done
    ``` -/
elab stx:"show_puzzle" : tactic =>
  Widget.savePanelWidgetInfo
    (hash AkariPanelWidget.javascript)
    (return .null)
    stx

end Akari
