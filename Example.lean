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
