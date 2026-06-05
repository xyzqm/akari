import Lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Prod
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
def Pos (n m : Nat) := Fin n × Fin m deriving DecidableEq, Fintype

def Pos.r (p : Pos n m) := p.1
def Pos.c (p : Pos n m) := p.2

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
               then [⟨⟨r - 1, by omega⟩, p.c⟩]
               else []

  let down  := if h : r + 1 < puz.rows
               then [⟨⟨r + 1, h⟩, p.c⟩]
               else []

  let left  := if h : c > 0
               then [⟨p.r, ⟨c - 1, by omega⟩⟩]
               else []

  let right := if h : c + 1 < puz.cols
               then [⟨p.r, ⟨c + 1, h⟩⟩]
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

/-! # Decidability for Sees -/

/-- `Sees puz p1 p2` is decidable for concrete puzzles. -/
instance (puz : Puzzle) (p1 p2 : puz.Pos) : Decidable (Sees puz p1 p2) := by
  unfold Sees
  split_ifs with hr hc
  · exact Fintype.decidableForallFintype
  · exact Fintype.decidableForallFintype
  · exact instDecidableFalse

/-! # Uniqueness helper lemmas -/

/-- If a #n black cell has exactly n neighbors (so every neighbor must be a bulb),
    then every neighbor is in `sol`. -/
theorem IsSolution.forced_bulb
    {puz : Puzzle} {sol : Finset puz.Pos}
    (h    : IsSolution puz sol)
    (pos  : puz.Pos)
    (n    : Fin 5)
    (hcell  : puz.cells pos = Cell.black (some n))
    (q      : puz.Pos)
    (hq_mem : q ∈ getNeighbors puz pos)
    (hlen   : (getNeighbors puz pos).length = n.val)
    : q ∈ sol := by
  have hadj := h.adj_correct pos
  simp only [hcell] at hadj
  -- Unify the two alpha-equivalent filter predicates so omega can use both.
  have hadj' : (List.filter (· ∈ sol) (getNeighbors puz pos)).length = n.val := hadj
  -- A sublist with the same length as the original must equal the original.
  have hfull : List.filter (· ∈ sol) (getNeighbors puz pos) = getNeighbors puz pos :=
    List.Sublist.eq_of_length_le List.filter_sublist (by omega)
  -- q is in the filter because the filter equals the original list.
  have hq_in_filter : q ∈ List.filter (· ∈ sol) (getNeighbors puz pos) := by
    rw [hfull]; exact hq_mem
  -- List.mem_filter gives: q ∈ l ∧ decide (q ∈ sol) = true
  exact of_decide_eq_true (List.mem_filter.mp hq_in_filter).2

/-- Empty-aware generalisation of `forced_bulb`: if some neighbors of a #n black
    cell are already known to be empty (`∉ sol`), and the remaining *free*
    neighbors number exactly `n`, then every free neighbor is a bulb. -/
theorem IsSolution.forced_bulb_filter
    {puz : Puzzle} {sol : Finset puz.Pos}
    (h    : IsSolution puz sol)
    (pos  : puz.Pos)
    (n    : Fin 5)
    (hcell    : puz.cells pos = Cell.black (some n))
    (empties  : List puz.Pos)
    (hempties : ∀ e ∈ empties, e ∉ sol)
    (hlen     : ((getNeighbors puz pos).filter (· ∉ empties)).length = n.val)
    (q        : puz.Pos)
    (hq_mem   : q ∈ getNeighbors puz pos)
    (hq_free  : q ∉ empties)
    : q ∈ sol := by
  have hadj := h.adj_correct pos
  simp only [hcell] at hadj
  have hadj' : (List.filter (· ∈ sol) (getNeighbors puz pos)).length = n.val := hadj
  -- Every in-`sol` neighbor is non-empty, so `filter (· ∈ sol)` is a sublist of
  -- `filter (· ∉ empties)`.
  have himp : ∀ a : puz.Pos, (decide (a ∈ sol) = true) → (decide (a ∉ empties) = true) := by
    intro a ha
    have ha' : a ∈ sol := of_decide_eq_true ha
    have hne : a ∉ empties := fun hae => (hempties a hae) ha'
    simpa using hne
  have hsub : List.Sublist (List.filter (· ∈ sol) (getNeighbors puz pos))
                           (List.filter (· ∉ empties) (getNeighbors puz pos)) :=
    List.monotone_filter_right _ himp
  -- Equal lengths (`= n.val`) force the two filters to be equal lists.
  have heq : List.filter (· ∈ sol) (getNeighbors puz pos)
           = List.filter (· ∉ empties) (getNeighbors puz pos) :=
    hsub.eq_of_length (by rw [hadj', hlen])
  have hq_in : q ∈ List.filter (· ∉ empties) (getNeighbors puz pos) :=
    List.mem_filter.mpr ⟨hq_mem, by simpa using hq_free⟩
  rw [← heq] at hq_in
  exact of_decide_eq_true (List.mem_filter.mp hq_in).2

/-- If `q ∈ sol` and `p` sees `q`, then `p ∉ sol`. -/
theorem IsSolution.forced_empty_of_sees
    {puz : Puzzle} {sol : Finset puz.Pos}
    (h   : IsSolution puz sol)
    (p q : puz.Pos)
    (hq  : q ∈ sol)
    (hpq : Sees puz p q)
    (hne : p ≠ q)
    : p ∉ sol := fun hp =>
  h.no_conflicts p q hne hp hq hpq

/-- Lighting deduction: a white cell `q` must be illuminated, so it sees *some*
    bulb. If every cell `q` can see — other than `q` itself — is known empty
    (`∉ sol`), then the bulb lighting `q` can only be `q`, hence `q ∈ sol`.

    `visible` is the list of cells `q` sees apart from itself; `hvis` says it is
    exhaustive (anything `q` sees is `q` or in `visible`). -/
theorem IsSolution.forced_lit
    {puz : Puzzle} {sol : Finset puz.Pos}
    (h       : IsSolution puz sol)
    (q       : puz.Pos)
    (hwhite  : puz.cells q = Cell.white)
    (visible : List puz.Pos)
    (hvis    : ∀ v, Sees puz q v → v = q ∨ v ∈ visible)
    (hempty  : ∀ v ∈ visible, v ∉ sol)
    : q ∈ sol := by
  obtain ⟨b, hb_mem, hb_sees⟩ := h.all_lit q hwhite
  rcases hvis b hb_sees with hbq | hbvis
  · exact hbq ▸ hb_mem
  · exact absurd hb_mem (hempty b hbvis)

end Akari
