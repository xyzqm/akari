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
abbrev mySolution : Finset myPuzzle.Pos := {⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩}

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
    dsimp [AllWhiteCellsLit, IsIlluminated, Sees]
    intro ⟨r, c⟩
    fin_cases r <;> fin_cases c <;> decide
  · -- adj_correct: The black cell at (1,1) has exactly 4 adjacent bulbs
    dsimp [AdjacencyCorrect, myPuzzle, mySolution, getNeighbors]
    intro ⟨r, c⟩
    fin_cases r <;> fin_cases c <;> simp_all
    <;> split_ifs
    <;> simp_all
    <;> trivial

#eval match Cell.black (some 2) with
| Cell.black (some n) => 2 = n
| _ => True
