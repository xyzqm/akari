import Akari
import Mathlib.Tactic
open Akari

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
def mySolution : Finset myPuzzle.Pos := {⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩}

/-- We want to prove this is a valid solution -/
theorem solved_example : IsSolution myPuzzle mySolution := by
  constructor
  · -- no_conflicts: The 4 bulbs can't see each other because the black cell blocks them
    rw [NoBulbConflicts]
    intro p1 p2 neq h1 h2
    fin_cases h1 <;> fin_cases h2
    <;> dsimp [Sees]
    <;> simp_all <;> decide
  · -- all_lit: Every white cell sees one of the 4 bulbs
    dsimp [AllWhiteCellsLit, IsIlluminated, IsInBounds, myPuzzle, mySolution, Sees]
    intro p ⟨hr, hc⟩ hwhite
    omega
  · -- adj_correct: The black cell at (1,1) has exactly 4 adjacent bulbs
    dsimp [AdjacencyCorrect, IsInBounds, myPuzzle, mySolution]
    intro p ⟨hr, hc⟩
    split
    · -- This is the black cell at (1,1) with value 4
      simp [Pos.mk]
      decide
    · decide
    · decide
