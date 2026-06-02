# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build commands

```bash
lake build                    # build the Akari library (default target)
lake env lean Example.lean    # type-check Example.lean (not a lake target)
lake exe akari                # run the main executable (currently a stub)
```

`Main.lean` has a pre-existing compile error (`Unknown identifier 'hello'`) — this is expected and unrelated to library work.

## Project structure

- **`Akari/Basic.lean`** — all core definitions: `Cell`, `Pos`, `Puzzle`, the three rule predicates (`NoBulbConflicts`, `AllWhiteCellsLit`, `AdjacencyCorrect`), `IsSolution`, and `getNeighbors`.
- **`Akari/Tactics/Basic.lean`** — all custom proof tactics (described below). Opens `Lean Elab Term Tactic Meta`.
- **`Akari.lean`** — top-level module that re-exports `Akari.Basic` and `Akari.Tactics.Basic`.
- **`Example.lean`** — reference proof for a 3×3 puzzle; used as the primary integration test.

## Core types

```lean
Cell       ::= black (Option (Fin 5)) | white
Pos n m    := Fin n × Fin m            -- grid coordinate
Puzzle     ::= { rows cols : Nat; cells : Pos rows cols → Cell }
IsSolution puz sol : Prop              -- sol : Finset puz.Pos
```

`IsSolution` bundles three predicates:
- `NoBulbConflicts` — no two bulbs share a line of sight
- `AllWhiteCellsLit` — every white cell sees at least one bulb
- `AdjacencyCorrect` — each numbered black cell has exactly that many adjacent bulbs

## Proof model

The goal stays `IsSolution puz sol` throughout a tactic proof. Each tactic reads `puz` and `sol` from the goal automatically and accumulates hypotheses in the local context:

- `hbulb_N : pos ∈ sol` — cell is a confirmed bulb
- `hempty_N : pos ∉ sol` — cell is confirmed empty

`isBulbHyp` / `isEmptyHyp` detect these by checking `fn == ``Membership.mem`. **Critical layout note:** in Lean 4.30's `@Membership.mem α β inst` application, `args = [α, β, inst, SET, ELEMENT]` — the SET is at `args[args.size - 2]` and the ELEMENT is at `args.back!` (opposite of what the class definition implies).

## Available tactics (`Akari.Tactics`)

| Tactic | Argument | Effect |
|---|---|---|
| `forced_lights pos` | position of a **black #n cell** | adds `hbulb_i : q ∈ sol` for every white neighbor `q` |
| `forced_xs pos` | position of a **white cell** | adds `hempty : pos ∉ sol` |
| `mark_lit_xs` | (none) | for every white cell currently seen by a placed bulb, adds `hempty_i : cell ∉ sol` |
| `suffocated pos` | position of a **black cell** | closes a `False` goal when the cell cannot satisfy its count constraint |
| `akari_done` | (none) | closes `IsSolution puz sol` using `fin_cases` + `decide`/`simp` on the three sub-goals |

Typical proof structure:

```lean
theorem my_proof : IsSolution myPuzzle mySolution := by
  forced_lights ⟨r, c⟩   -- black #n cell with exactly n free neighbors
  mark_lit_xs              -- auto-mark cells visible from placed bulbs
  forced_xs ⟨r', c'⟩     -- any remaining empties that need explicit reasoning
  akari_done
```

## Key implementation details

**Kernel evaluation pattern** — tactics evaluate concrete Lean expressions using `withTransparency .all (reduce ...)` or `withTransparency .all (whnf ...)`. Plain `whnf` (default transparency) does NOT unfold regular `def`s like `Pos.r`, `Pos.c`, or `Nat.sub` — always use `.all` for evaluating puzzle cells or neighbor lists.

**`posRowCol`** — converts a `Fin n × Fin m` `Expr` to `(Nat × Nat)` by calling `reduce` with `.all` transparency. Used to extract concrete coordinates from hypothesis element expressions.

**`exprListElems`** — walks a `List α` `Expr` iteratively (not recursively, to avoid Lean's termination checker) using `withTransparency .all (whnf ...)`.

**`forced_lights` internals** — calls `getNeighbors puz pos` via `exprListElems`, extracts numeric row/col via `posRowCol`, then generates `have hbulb : ⟨r, c⟩ ∈ sol := by native_decide` using numeric literal syntax to avoid typeclass ambiguity.

**`akari_done` limitation** — closes proofs using `fin_cases` + `decide`, which works for small concrete puzzles. `native_decide` cannot close `IsSolution` directly because `Decidable (IsSolution puz sol)` instances are not automatically synthesized.

**`delab` for sol** — `sol` is passed to `have` tactics via `Lean.PrettyPrinter.delab solExpr`. This works reliably for global `abbrev` solutions but may produce verbose output for inline definitions.
