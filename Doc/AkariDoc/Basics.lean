import VersoManual
import Akari.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Akari

#doc (Manual) "Core Definitions" =>

%%%
tag := "basics"
%%%

This chapter walks through every definition in `Akari/Basic.lean`. The goal is to
show how a familiar logic puzzle translates into Lean 4's type system — no prior
Lean experience required.

# Cells and Grid Positions

## The `Cell` Type

In Akari, every square on the grid is either white (a candidate bulb location) or
black (a wall). Black cells optionally carry a small digit from 0 to 4, indicating
how many of their direct neighbors must contain bulbs.

```
inductive Cell where
  | black : Option (Fin 5) → Cell
  | white : Cell
  deriving BEq, DecidableEq, Inhabited
```

`Cell` is an *inductive type* — Lean's version of a tagged union or enum-with-data.
It has two constructors:

- `Cell.black (Option (Fin 5))` — a black cell whose optional number is either
  `none` (unnumbered) or `some n` where `n : Fin 5`.  `Fin 5` is Lean's type for
  natural numbers strictly less than 5, so values 0, 1, 2, 3, or 4.
- `Cell.white` — carries no data.

The `deriving` clause asks Lean to automatically generate three type class
instances: `BEq` (boolean equality), `DecidableEq` (propositional equality
that can be decided by a program), and `Inhabited` (a proof that the type has
at least one element — Lean picks `Cell.white` here).

## Positions: `Pos n m`

A grid position is a pair *(row, column)*, but we want the compiler to
prevent out-of-bounds coordinates entirely:

```
def Pos (n m : Nat) := Fin n × Fin m
```

`Fin n` is the type of natural numbers *strictly less than n*.  A value of type
`Fin n` carries both a number and a proof that the number is in bounds.  So
`Pos 3 3` is the type of pairs `(r, c)` where `0 ≤ r < 3` and `0 ≤ c < 3` —
exactly the nine squares of a 3×3 grid.  There is no runtime bounds check
because the constraint is enforced at the type level.

Two projection helpers extract the components:

```
def Pos.r (p : Pos n m) := p.1   -- row
def Pos.c (p : Pos n m) := p.2   -- column
```

# Puzzles and Proof State

## The `Puzzle` Structure

```
structure Puzzle where
  rows : Nat
  cols : Nat
  cells : Pos rows cols → Cell
```

A `Puzzle` bundles the grid dimensions with a *function* that maps every valid
position to its cell type.  Representing the grid as a function (rather than
a two-dimensional array) is the natural choice in Lean because it lets the
type checker treat grid queries as pure mathematical applications, without any
indexing or allocation overhead.

The `Puzzle.Pos` abbreviation just names the position type for a particular puzzle:

```
abbrev Puzzle.Pos (puz : Puzzle) : Type :=
  Akari.Pos puz.rows puz.cols
```

A concrete puzzle is just a `where`-block filling in the three fields.  For
example, the 3×3 grid used in `Example.lean` has a single black #4 cell at the
center, with everything else white:

```
abbrev myPuzzle : Puzzle where
  rows := 3
  cols := 3
  cells p :=
    if p == ⟨1, 1⟩ then Cell.black (some 4)
    else Cell.white
```

`⟨1, 1⟩` is anonymous-constructor notation for `(Fin.mk 1 _, Fin.mk 1 _)` —
Lean infers the bound proofs from the goal type.

## The `Mark` Type

```
inductive Mark where
  | bulb
  | empty
  | unknown
  deriving BEq, DecidableEq, Inhabited
```

`Mark` is a three-valued annotation used internally during proof construction to
track what is known about each cell: `bulb` (a bulb is placed here), `empty`
(definitely no bulb), or `unknown` (not yet determined).  It is *not* part of the
logical puzzle definition — it exists purely to let tactic implementations track
their progress.

# Visibility

## The `Sees` Predicate

Two cells *see* each other when they are in the same row or column and every
cell strictly between them is white:

```
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
```

`Sees` is a *proposition* — a type whose inhabitants are proofs.  The definition
branches on three cases:

1. *Same row* (`p1.r == p2.r`): scan the columns strictly between them.
   `min`/`max` make the scan direction-independent, so `Sees puz p q` and
   `Sees puz q p` are definitionally equal.
2. *Same column* (`p1.c == p2.c`): scan the rows strictly between them.
3. *Neither*: the proposition is `False`, meaning the cells cannot see each
   other at all.

Notice that `Sees puz p p` is vacuously true (the universal quantifier ranges
over an empty interval), so a bulb illuminates its own cell.

## `Seeing`: the Full Visibility Set

```
def Seeing (puz : Puzzle) (p : puz.Pos) : Set puz.Pos := { p2 | Sees puz p p2 }
```

`Seeing puz p` is the *set* of all positions visible from `p`.  In Lean 4, `Set α`
is just a predicate `α → Prop`, so `Seeing` is notation for the comprehension
`{ p2 | Sees puz p p2 }`.

## Decidability of `Sees`

For the proof tactics to call `decide` or `native_decide` on visibility queries,
Lean needs to know that `Sees` is *decidable* — that there is a terminating
algorithm which evaluates it to `true` or `false`:

```
instance (puz : Puzzle) (p1 p2 : puz.Pos) : Decidable (Sees puz p1 p2) := by
  unfold Sees
  split_ifs with hr hc
  · exact Fintype.decidableForallFintype
  · exact Fintype.decidableForallFintype
  · exact instDecidableFalse
```

The tactic proof unfolds `Sees`, splits the `if`-branches, and fills each branch
with a standard Mathlib lemma: `Fintype.decidableForallFintype` says that a
universally quantified predicate over a finite type is decidable (because you can
check all elements), and `instDecidableFalse` handles the impossible case.

# The Three Rules

## Rule 1: No Bulb Conflicts

```
def NoBulbConflicts (puz : Puzzle) (st : Finset puz.Pos) : Prop :=
  ∀ p1 p2, p1 ≠ p2 → p1 ∈ st → p2 ∈ st → ¬ Sees puz p1 p2
```

`st` is a `Finset puz.Pos` — a finite set of grid positions marking bulb
locations.  `NoBulbConflicts` says: for every pair of *distinct* bulbs in `st`,
they must not see each other.  The `p1 ≠ p2` guard prevents the rule from
complaining that a bulb conflicts with itself.

## Rule 2: All White Cells are Lit

A white cell is *illuminated* if at least one bulb in `st` can see it:

```
def IsIlluminated (puz : Puzzle) (st : Finset puz.Pos) (p : puz.Pos) : Prop :=
  ∃ p_bulb, p_bulb ∈ st ∧ Sees puz p p_bulb
```

The existential `∃ p_bulb, ...` means "there exists a position `p_bulb` such
that it is in the solution set and it sees `p`."  Then:

```
def AllWhiteCellsLit (puz : Puzzle) (st : Finset puz.Pos) : Prop :=
  ∀ p, puz.cells p = Cell.white → IsIlluminated puz st p
```

`AllWhiteCellsLit` universally quantifies over all positions and requires every
white cell to be illuminated.

## Neighbor Lists: `getNeighbors`

Before defining Rule 3 we need a helper that computes the adjacent cells (up,
down, left, right) of a given position, handling the grid boundary safely:

```
def getNeighbors (puz : Puzzle) (p : puz.Pos) : List puz.Pos :=
  let r := p.r.val
  let c := p.c.val
  have hr : r < puz.rows := p.r.isLt
  have hc : c < puz.cols := p.c.isLt
  let up    := if h : r > 0       then [⟨⟨r - 1, by omega⟩, p.c⟩]        else []
  let down  := if h : r + 1 < puz.rows then [⟨⟨r + 1, h⟩, p.c⟩]         else []
  let left  := if h : c > 0       then [⟨p.r, ⟨c - 1, by omega⟩⟩]        else []
  let right := if h : c + 1 < puz.cols then [⟨p.r, ⟨c + 1, h⟩⟩]         else []
  up ++ down ++ left ++ right
```

Each direction is a *dependent if-then-else*: the condition is a proposition
(`r > 0`, `r + 1 < puz.rows`, etc.) and the `then`-branch uses that proof to
construct the out-of-bounds-safe `Fin` value.  The `by omega` tactic discharges
arithmetic obligations like "if `r < rows` and `r > 0`, then `r - 1 < rows`"
automatically.  The result is a plain `List` — not a `Finset` — because order
matters for the `AdjacencyCorrect` count.

## Rule 3: Adjacency Counts are Correct

```
def AdjacencyCorrect (puz : Puzzle) (st : Finset puz.Pos) : Prop :=
  ∀ p,
    match puz.cells p with
    | Cell.black (some n) =>
      let neighbors := getNeighbors puz p
      let bulb_count := (neighbors.filter (λ n_pos => n_pos ∈ st)).length
      bulb_count = n.val
    | _ => True
```

For every position `p`, `AdjacencyCorrect` matches on the cell type.  If it is
a numbered black cell, the number of neighbors that are in the solution set must
equal `n.val` (the underlying `Nat` of the `Fin 5` digit).  All other cells
impose no constraint (`True`).  The `filter` call keeps only those neighbors
that appear in `st`; `.length` counts them.

# Solutions

## `IsSolution`

```
structure IsSolution (puz : Puzzle) (st : Finset puz.Pos) : Prop where
  no_conflicts : NoBulbConflicts puz st
  all_lit      : AllWhiteCellsLit puz st
  adj_correct  : AdjacencyCorrect puz st
```

`IsSolution` is a *proof-relevant structure* — its inhabitants are proofs, not
data.  Given a puzzle `puz` and a candidate bulb set `st`, `IsSolution puz st`
holds exactly when all three rules are satisfied simultaneously.  The three named
fields are just the three proofs.

Proving `IsSolution puz st` therefore requires three sub-proofs, one per field.
In `Example.lean`, the theorem `solved_example` does this directly:

```
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
```

`constructor` splits the goal into the three fields.  `fin_cases` enumerates all
possible values of a finite type, turning a universally quantified statement into
finitely many concrete goals that `decide` can check.

# Helper Theorems

Two lemmas in `Akari/Basic.lean` encapsulate the two key logical deductions used
by the proof tactics.

## `IsSolution.forced_bulb`

If a numbered black cell `pos` has *exactly* `n` neighbors (matching its digit),
then every neighbor must be a bulb:

```
theorem IsSolution.forced_bulb
    {puz : Puzzle} {sol : Finset puz.Pos}
    (h    : IsSolution puz sol)
    (pos  : puz.Pos)
    (n    : Fin 5)
    (hcell  : puz.cells pos = Cell.black (some n))
    (q      : puz.Pos)
    (hq_mem : q ∈ getNeighbors puz pos)
    (hlen   : (getNeighbors puz pos).length = n.val)
    : q ∈ sol
```

The key insight in the proof is that `AdjacencyCorrect` tells us the *filter* of
the neighbor list by `sol`-membership has length `n.val`.  But the full neighbor
list also has length `n.val` (by `hlen`).  A sublist of the same length as the
original list must *equal* the original list (`List.Sublist.eq_of_length_le`),
so every neighbor is in the filter, which means every neighbor is in `sol`.

## `IsSolution.forced_empty_of_sees`

If `q` is a bulb and `p` can see `q` (and `p ≠ q`), then `p` cannot also be a bulb:

```
theorem IsSolution.forced_empty_of_sees
    {puz : Puzzle} {sol : Finset puz.Pos}
    (h   : IsSolution puz sol)
    (p q : puz.Pos)
    (hq  : q ∈ sol)
    (hpq : Sees puz p q)
    (hne : p ≠ q)
    : p ∉ sol
```

This follows immediately from `NoBulbConflicts`: if `p` were also in `sol`, it
would be a second bulb that sees `q`, violating the no-conflicts rule.
