import Akari
import Akari.Tactics.Basic
import Akari.Widget
import Mathlib.Tactic
open Akari Akari.Tactics

/-!
## 15×15 Puzzle (efficiency test)

Checkerboard of black cells:
  • `r%2 == 1 && c%2 == 1` → black #4 (49 cells — the numbered centers)
  • `r%2 == 0 && c%2 == 0` → black unnumbered (64 cells — block cross-room sight)
  • otherwise           → white (112 cells — all become forced bulbs)

Every white cell has exactly one odd coordinate and is adjacent to a #4 center
(forced bulb).  The two black cell types are each adjacent to a forced bulb, so
`mark_conflict_xs` marks all of them empty.  After 49 `forced_bulbs` +
`mark_conflict_xs`, every position is determined and `uniqueness_done` closes.
-/

abbrev bigPuzzle : Puzzle where
  rows := 15
  cols := 15
  cells p :=
    if p.1.val % 2 == 1 && p.2.val % 2 == 1 then Cell.black (some 4)
    else if p.1.val % 2 == 0 && p.2.val % 2 == 0 then Cell.black none
    else Cell.white

abbrev bigSolution : Finset bigPuzzle.Pos :=
  Finset.univ.filter fun p => p.1.val % 2 ≠ p.2.val % 2

-- Note: `uniqueness_done` proves a single `native_decide` "bridge" relating `bigSolution`
-- to a synthesized 2D bool lookup table, then does `fin_cases` over 225 positions; each
-- goal closes by `assumption` (∈ sol side) + a shallow table `decide` (membership side).
-- This is representation-independent (works for set-literal solutions too) and avoids
-- evaluating the 225-element Finset per cell. 15×15 compiles in ~1 min, ~800K heartbeats.
set_option linter.unusedTactic false in
set_option maxHeartbeats 1000000 in
theorem bigPuzzle_unique_visual : ∀ sol, IsSolution bigPuzzle sol → sol = bigSolution := by with_panel_widgets [AkariPanelWidget]
  intro sol h
  forced_bulbs_only ⟨1,1⟩; forced_bulbs_only ⟨1,3⟩; forced_bulbs_only ⟨1,5⟩; forced_bulbs_only ⟨1,7⟩; forced_bulbs_only ⟨1,9⟩; forced_bulbs_only ⟨1,11⟩; forced_bulbs_only ⟨1,13⟩
  forced_bulbs_only ⟨3,1⟩; forced_bulbs_only ⟨3,3⟩; forced_bulbs_only ⟨3,5⟩; forced_bulbs_only ⟨3,7⟩; forced_bulbs_only ⟨3,9⟩; forced_bulbs_only ⟨3,11⟩; forced_bulbs_only ⟨3,13⟩
  forced_bulbs_only ⟨5,1⟩; forced_bulbs_only ⟨5,3⟩; forced_bulbs_only ⟨5,5⟩; forced_bulbs_only ⟨5,7⟩; forced_bulbs_only ⟨5,9⟩; forced_bulbs_only ⟨5,11⟩; forced_bulbs_only ⟨5,13⟩
  forced_bulbs_only ⟨7,1⟩; forced_bulbs_only ⟨7,3⟩; forced_bulbs_only ⟨7,5⟩; forced_bulbs_only ⟨7,7⟩; forced_bulbs_only ⟨7,9⟩; forced_bulbs_only ⟨7,11⟩; forced_bulbs_only ⟨7,13⟩
  forced_bulbs_only ⟨9,1⟩; forced_bulbs_only ⟨9,3⟩; forced_bulbs_only ⟨9,5⟩; forced_bulbs_only ⟨9,7⟩; forced_bulbs_only ⟨9,9⟩; forced_bulbs_only ⟨9,11⟩; forced_bulbs_only ⟨9,13⟩
  forced_bulbs_only ⟨11,1⟩; forced_bulbs_only ⟨11,3⟩; forced_bulbs_only ⟨11,5⟩; forced_bulbs_only ⟨11,7⟩; forced_bulbs_only ⟨11,9⟩; forced_bulbs_only ⟨11,11⟩; forced_bulbs_only ⟨11,13⟩
  forced_bulbs_only ⟨13,1⟩; forced_bulbs_only ⟨13,3⟩; forced_bulbs_only ⟨13,5⟩; forced_bulbs_only ⟨13,7⟩; forced_bulbs_only ⟨13,9⟩; forced_bulbs_only ⟨13,11⟩; forced_bulbs_only ⟨13,13⟩
  mark_conflict_xs
  uniqueness_done
