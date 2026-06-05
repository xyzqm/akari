import Akari
import Akari.Tactics.Basic
import Akari.Widget
import Mathlib.Tactic
open Akari Akari.Tactics

/-!
# Example Puzzle

A simple 3x3 grid:
W W W
W 4 W
W W W

(Note: coordinates are (row, col))
-/

abbrev myPuzzle : Puzzle where
  rows := 3
  cols := 3
  cells p :=
    if p == ⟨1, 1⟩ then Cell.black (some 4)
    else Cell.white

/-- A proposed solution state: bulbs around the central black cell -/
abbrev mySolution : Finset myPuzzle.Pos := {⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩}

/-- Original proof using fin_cases + decide -/
theorem solved_example : IsSolution myPuzzle mySolution := by
  constructor
  · rw [NoBulbConflicts]
    intro p1 p2 neq h1 h2
    fin_cases h1 <;> fin_cases h2
    <;> dsimp [Sees]
    <;> simp_all <;> decide
  · intro p
    dsimp [IsIlluminated, Sees]
    fin_cases p <;> decide
  · intro p
    fin_cases p <;> simp_all (config := { decide := true })

/-- Proof using akari_done directly. -/
theorem solved_example_tactics : IsSolution myPuzzle mySolution := by
  akari_done

/-- Uniqueness: mySolution is the ONLY valid solution to myPuzzle. -/
theorem myPuzzle_unique : ∀ sol, IsSolution myPuzzle sol → sol = mySolution := by
  intro sol h
  -- The #4 cell at ⟨1,1⟩ forces all 4 neighbors to be bulbs
  forced_bulbs ⟨1, 1⟩
  -- Every white cell that sees a bulb cannot also be a bulb
  mark_conflict_xs
  -- Close sol = mySolution using accumulated hbulb/hempty facts
  uniqueness_done

set_option linter.unusedTactic false in
/-- Visual walkthrough: place the cursor on each `show_puzzle` line to see the
    grid at that proof step.  Or use `with_panel_widgets [AkariPanelWidget]`
    once for an auto-updating view that follows the cursor. -/
theorem myPuzzle_unique_visual : ∀ sol, IsSolution myPuzzle sol → sol = mySolution := by with_panel_widgets [AkariPanelWidget]
  intro sol h
  forced_bulbs ⟨1, 1⟩
  mark_conflict_xs
  uniqueness_done

/-!
## 9×9 Puzzle (efficiency test)

Same checkerboard design scaled up:
  • `r%2 == 1 && c%2 == 1` → black #4 (16 centers)
  • `r%2 == 0 && c%2 == 0` → black unnumbered (25 corner separators)
  • otherwise              → white (40 forced bulbs)

16 `forced_bulbs` calls + `mark_conflict_xs` determine all 81 cells.
See `Example15.lean` for the same design at 15×15 (needs higher heartbeats).
-/

abbrev bigPuzzle : Puzzle where
  rows := 9
  cols := 9
  cells p :=
    if p.1.val % 2 == 1 && p.2.val % 2 == 1 then Cell.black (some 4)
    else if p.1.val % 2 == 0 && p.2.val % 2 == 0 then Cell.black none
    else Cell.white

abbrev bigSolution : Finset bigPuzzle.Pos :=
  Finset.univ.filter fun p => p.1.val % 2 ≠ p.2.val % 2

set_option linter.unusedTactic false in
theorem bigPuzzle_unique_visual : ∀ sol, IsSolution bigPuzzle sol → sol = bigSolution := by with_panel_widgets [AkariPanelWidget]
  intro sol h
  forced_bulbs ⟨1,1⟩; forced_bulbs ⟨1,3⟩; forced_bulbs ⟨1,5⟩; forced_bulbs ⟨1,7⟩
  forced_bulbs ⟨3,1⟩; forced_bulbs ⟨3,3⟩; forced_bulbs ⟨3,5⟩; forced_bulbs ⟨3,7⟩
  forced_bulbs ⟨5,1⟩; forced_bulbs ⟨5,3⟩; forced_bulbs ⟨5,5⟩; forced_bulbs ⟨5,7⟩
  forced_bulbs ⟨7,1⟩; forced_bulbs ⟨7,3⟩; forced_bulbs ⟨7,5⟩; forced_bulbs ⟨7,7⟩
  mark_conflict_xs
  uniqueness_done
