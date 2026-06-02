import Akari
import Akari.Tactics.Basic
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

/-- New proof using Akari tactics.
    The #4 black cell at ⟨1,1⟩ has exactly 4 white neighbors, so all are forced bulbs.
    The 4 corner cells are forced empty.
    The center black cell itself is not white, so coverage is over the 8 white cells. -/
theorem solved_example_tactics : IsSolution myPuzzle mySolution := by
  -- The #4 cell at ⟨1,1⟩ has exactly 4 white neighbors → all are forced bulbs
  forced_lights ⟨1, 1⟩
  -- Every white cell that can see one of the 4 bulbs is marked empty automatically
  mark_lit_xs
  akari_done
