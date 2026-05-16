import Lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
open Set

namespace Akari

/-! # Core Data Structures -/

/-- A cell is either black (with an optional number 0-4) or white. -/
inductive Cell where
  | black : Option (Fin 5) → Cell
  | white : Cell
  deriving BEq, DecidableEq, Inhabited

/-- Position on the grid. -/
structure Pos (n m : Nat) where
  r : Fin n
  c : Fin m
  deriving BEq, DecidableEq, Hashable

/-- An Akari puzzle definition. -/
structure Puzzle where
  rows : Nat
  cols : Nat
  cells : Pos rows cols → Cell

abbrev Puzzle.Pos (puz : Puzzle) : Type :=
  Akari.Pos puz.rows puz.cols

/-- Possible states for a cell during a proof. -/
inductive Mark where
  | bulb    -- A bulb is placed here
  | empty   -- Definitely not a bulb
  | unknown -- Not yet determined
  deriving BEq, DecidableEq, Inhabited

/-! # Rule Predicates -/

/-- Two positions can "see" each other if they are in the same row/column
    and there are no black cells between them. -/
def Sees (puz : Puzzle) (p1 p2 : puz.Pos) : Prop :=
  if p1.r == p2.r then
    let r := p1.r
    let c1 := min p1.c p2.c
    let c2 := max p1.c p2.c
    ∀ c, c1 < c ∧ c < c2 → puz.cells ⟨r, c⟩ = Cell.white
  else if p1.c == p2.c then
    let c := p1.c
    let r1 := min p1.r p2.r
    let r2 := max p1.r p2.r
    ∀ r, r1 < r ∧ r < r2 → puz.cells ⟨r, c⟩ = Cell.white
  else
    False

/-- The set of cells that can see a given cell. -/
def Seeing (puz : Puzzle) (p : puz.Pos) : Set puz.Pos := { p2 | Sees puz p p2 }

/-- A white cell is illuminated if it can see a bulb. -/
def IsIlluminated (puz : Puzzle) (st : Finset puz.Pos) (p : puz.Pos) : Prop :=
  ∃ p_bulb, p_bulb ∈ st ∧ Sees puz p p_bulb

/-- Rule 1: No two bulbs can see each other. -/
def NoBulbConflicts (puz : Puzzle) (st : Finset puz.Pos) : Prop :=
  ∀ p1 p2, p1 ≠ p2 → p1 ∈ st → p2 ∈ st → ¬ Sees puz p1 p2

/-- Rule 2: Every white cell must be illuminated. -/
def AllWhiteCellsLit (puz : Puzzle) (st : Finset puz.Pos) : Prop :=
  ∀ p, puz.cells p = Cell.white → IsIlluminated puz st p

-- Put this helper function before your validation logic
def getNeighbors (puz : Puzzle) (p : puz.Pos) : List puz.Pos :=
  let r := p.r.val
  let c := p.c.val

  -- Extract the proofs that our current position is within bounds
  have hr : r < puz.rows := p.r.isLt
  have hc : c < puz.cols := p.c.isLt

  -- Safely build each neighbor. If the condition is false, return an empty list [].
  -- `omega` automatically proves things like "if r < rows and r > 0, then r - 1 < rows".
  let up    := if h : r > 0
               then [(⟨⟨r - 1, by omega⟩, p.c⟩ : puz.Pos)]
               else []

  let down  := if h : r + 1 < puz.rows
               then [({ r := ⟨r + 1, h⟩, c := p.c } : puz.Pos)]
               else []

  let left  := if h : c > 0
               then [({ r := p.r, c := ⟨c - 1, by omega⟩ } : puz.Pos)]
               else []

  let right := if h : c + 1 < puz.cols
               then [({ r := p.r, c := ⟨c + 1, h⟩ } : puz.Pos)]
               else []

  -- Combine all valid neighbors into one list
  up ++ down ++ left ++ right
/-- Rule 3: Numbered black cells must have exactly that many adjacent bulbs. -/
def AdjacencyCorrect (puz : Puzzle) (st : Finset puz.Pos) : Prop :=
  ∀ p,
    match puz.cells p with
    | Cell.black (some n) =>
      let neighbors := getNeighbors puz p
      let bulb_count := (neighbors.filter (λ n_pos => n_pos ∈ st)).length
      bulb_count = n.val
    | _ => True

/-- A solution is a Finset Pos where every cell is decided (bulb or empty)
    and all rules are satisfied. -/
structure IsSolution (puz : Puzzle) (st : Finset puz.Pos) : Prop where
  no_conflicts : NoBulbConflicts puz st
  all_lit : AllWhiteCellsLit puz st
  adj_correct : AdjacencyCorrect puz st

end Akari
