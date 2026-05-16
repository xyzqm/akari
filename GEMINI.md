# Akari (Light Up) Formalization Project

## Project Overview
This project aims to formalize the logic and rules of the Akari (Light Up) puzzle game using the **Lean 4** theorem prover. The goal is to create a "proof-carrying game" environment where players can solve puzzles by providing formal proofs for each move, ensuring correctness through Lean's kernel. It is inspired by projects like `LeanSudoku`.

### Main Technologies
- **Lean 4**: The primary language for formalization and proof automation.
- **Lake**: Lean's build system and package manager.

### Architecture
- `Akari/Basic.lean`: Defines the core data structures (`Cell`, `Pos`, `Puzzle`, `Finset Pos`) and the fundamental rules (`NoBulbConflicts`, `AllWhiteCellsLit`, `AdjacencyCorrect`).
- `Akari/Tactics/`: Intended for custom Lean tactics to automate common puzzle-solving steps (e.g., `bulb_at`).
- `Example.lean`: Demonstrates how to define a puzzle and attempt a formal solution.

## Building and Running
The project uses the standard Lean 4 `lake` build system.

- **Build the project:**
  ```bash
  lake build
  ```
- **Run the main executable:**
  ```bash
  lake exe akari
  ```
- **Run tests (if added):**
  ```bash
  lake test
  ```

## Development Conventions
- **Naming:** Follows Lean 4 conventions (CamelCase for types and structures, snake_case or camelCase for definitions and theorems depending on context, though the current codebase uses CamelCase for most definitions).
- **Formalization:** Every game rule must be represented as a `Prop`. A puzzle is considered "solved" only when a term of type `IsSolution puzzle state` is constructed.
- **Proof Style:** Aim for interactive proof development using tactics. Custom tactics should be placed in `Akari/Tactics/`.
- **Modularity:** Keep core definitions in `Akari/Basic.lean` and separate automation logic into the `Tactics` directory.
