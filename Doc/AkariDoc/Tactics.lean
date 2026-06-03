import VersoManual
import Akari.Basic
import Akari.Tactics.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Akari Akari.Tactics

#doc (Manual) "Proof Tactics" =>

%%%
tag := "tactics"
%%%

This chapter explains every tactic in `Akari/Tactics/Basic.lean`.  The chapter
assumes you have read the previous one; concepts like `IsSolution`, `Finset`,
and `Sees` are used without re-introduction.

# The Proof Model

A standard Lean tactic proof for Akari looks like this:

```
theorem myPuzzle_unique : ∀ sol, IsSolution myPuzzle sol → sol = mySolution := by
  intro sol h
  forced_bulbs ⟨1, 1⟩
  mark_conflict_xs
  uniqueness_done
```

The proof *goal* — the statement being proved — starts as
`∀ sol, IsSolution myPuzzle sol → sol = mySolution` and becomes
`sol = mySolution` after `intro sol h` binds the universal and introduces
`h : IsSolution myPuzzle sol` as a hypothesis.

Throughout the proof, every Akari tactic *leaves the goal unchanged* and instead
adds new *hypotheses* to the local context.  By convention, hypotheses take two
forms:

- `hbulb_i : q ∈ sol` — cell `q` is a confirmed bulb
- `hempty_j : q ∉ sol` — cell `q` is confirmed empty

Once enough such facts accumulate, a closing tactic (`akari_done` or
`uniqueness_done`) can finish the proof.

There are two families of tactics:

- *Verification* tactics (`forced_xs`, `suffocated`, `akari_done`) are used when the
  goal is `IsSolution puz sol` — they check that a specific candidate solution is valid.
- *Uniqueness* tactics (`forced_bulbs`, `mark_conflict_xs`, `uniqueness_done`) are used
  when the goal is `sol = mySolution` — they prove that a solution is the unique one.

# Helper Utilities

## Parsing the Goal: `parseSolutionGoal`

```
def parseSolutionGoal (target : Expr) : MetaM (Expr × Expr) := do
  let target ← whnf target
  let (fn, args) := target.getAppFnArgs
  unless fn == ``Akari.IsSolution && args.size == 2 do
    throwError "expected goal of the form `IsSolution puz sol`, got {target}"
  return (args[0]!, args[1]!)
```

Lean 4 proof terms are represented as `Expr` values — a tree of constructors,
applications, and constants.  `parseSolutionGoal` takes the current goal
expression, reduces it to *weak head normal form* (`whnf`) to peel off any
top-level definitions, then uses `getAppFnArgs` to split it into the applied
function (`fn`) and its arguments (`args`).  When `fn` is `IsSolution` with two
arguments, the two arguments are the puzzle and the solution set.

`MetaM` is Lean's *meta-programming monad* — the monad for code that manipulates
proof terms.  The `←` is `do`-notation for monadic binding (equivalent to
`await` in async code or `>>=` in Haskell).

## Proving Ground Facts: `proveByNativeDecide`

```
def proveByNativeDecide (prop : Expr) : TacticM Expr := do
  let mvar ← mkFreshExprMVar prop MetavarKind.syntheticOpaque
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| native_decide))
  setGoals savedGoals
  instantiateMVars mvar
```

When a tactic needs to produce a proof of a concrete proposition (like
`⟨0, 1⟩ ∈ mySolution`), it uses this helper.  The pattern is:

1. Create a fresh *metavariable* (a proof-shaped hole) with type `prop`.
2. Temporarily make that hole the current goal.
3. Run `native_decide` on it — this compiles the proposition to native code and
   evaluates it; if it evaluates to `true`, the hole is filled.
4. Restore the original goals.
5. Return the filled proof term.

`native_decide` is fast but requires the proposition to be *decidable* (see the
`Decidable` instance for `Sees` in the previous chapter).

## Adding a Hypothesis: `addHyp`

```
def addHyp (name : Name) (proof : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let (_, newGoal) ← goal.note name proof
  replaceMainGoal [newGoal]
```

`goal.note name proof` inserts a new named hypothesis into the local context of
`goal`, returning the updated goal.  `replaceMainGoal` makes that updated goal
the current one.

# Hypothesis Inspection

## The `@Membership.mem` Argument Layout

`isBulbHyp` and `isEmptyHyp` detect hypotheses of the form `q ∈ sol` and
`q ∉ sol` respectively.  To do so, they inspect the internal `Expr` structure.

A membership expression `q ∈ sol` elaborates as
`@Membership.mem α β inst SET ELEMENT`, a five-argument application where the
arguments are: (0) `α` — element type; (1) `β` — container type; (2) `inst` — the
`Membership` instance; (3) `SET` — the set/container; (4) `ELEMENT` — the element
being tested.

Critically, the *set* is at `args[args.size - 2]` and the *element* is at
`args.back!` (the last argument).  This is the opposite of the class declaration
`Membership.mem : α → β → Prop` — the application stores arguments in the order
`(SET, ELEMENT)`, not `(ELEMENT, SET)`.

```
def isBulbHyp (hyp : LocalDecl) (solExpr : Expr) : MetaM Bool := do
  let (fn, args) := hyp.type.getAppFnArgs
  if fn == ``Membership.mem && args.size >= 2 then
    return ← isDefEq args[args.size - 2]! solExpr
  return false
```

`isDefEq` checks *definitional equality* — not just syntactic equality but also
equality up to unfolding definitions and reducing applications.

```
def isEmptyHyp (hyp : LocalDecl) (solExpr : Expr) : MetaM Bool := do
  let (fn, args) := hyp.type.getAppFnArgs
  if fn == ``Not && args.size == 1 then
    let (fn2, args2) := args[0]!.getAppFnArgs
    if fn2 == ``Membership.mem && args2.size >= 2 then
      return ← isDefEq args2[args2.size - 2]! solExpr
  return false
```

`isEmptyHyp` first checks for `Not` (one argument), then inspects the inner
`Membership.mem` application.

`bulbPos` and `emptyPos` extract the element from a `q ∈ sol` or `q ∉ sol`
hypothesis respectively by taking `args.back!`.

# Expression Utilities

## `finValNat`: Extracting a `Nat` from a `Fin`

```
def finValNat (e : Expr) : MetaM Nat := do
  let e' ← withTransparency .all (whnf e)
  if e'.isAppOfArity ``Fin.mk 3 then
    let valExpr := e'.getAppArgs[1]!
    let v ← withTransparency .all (reduce valExpr)
    match v with
    | .lit (.natVal n) => return n
    | bad => throwError "finValNat: could not reduce Fin.val to Nat literal, got {bad}"
  else ...
```

The key phrase is `withTransparency .all`.  Lean's type-checker has four
*transparency levels* controlling which definitions it will unfold during
reduction.  The default level (`default`) does *not* unfold regular `def`s — it
treats `Pos.r`, `Nat.sub`, and similar definitions as opaque.  Level `.all`
unfolds everything.  Without `.all`, `whnf` would leave `Fin.mk` wrapped inside
unevaluated `def` applications and the `isAppOfArity` check would fail.

`Fin.mk` takes three arguments: the bound `n` (implicit), the value, and the
proof that value `< n`.  So `e'.getAppArgs[1]!` retrieves the value at index 1.

## `posRowCol`: Extracting `(row, col)` from a `Pos`

```
def posRowCol (e : Expr) : MetaM (Nat × Nat) := do
  let e' ← withTransparency .all (reduce e)
  if e'.isAppOfArity ``Prod.mk 4 then
    let args := e'.getAppArgs
    return (← finValNat args[2]!, ← finValNat args[3]!)
  else
    throwError "posRowCol: expected Prod.mk after reduce, got {e'}"
```

`reduce` (unlike `whnf`) performs *full* reduction — β, ι (iota, for match
expressions), and δ (delta, for definitions).  After full reduction, a
`Pos = Fin n × Fin m` expression becomes `@Prod.mk (Fin rows) (Fin cols) r c`
with four arguments.  Arguments 2 and 3 are the `Fin` values; `finValNat`
extracts the underlying `Nat` from each.

## `exprListElems`: Walking a `List` Expression

```
def exprListElems (list : Expr) : MetaM (Array Expr) := do
  let mut elems : Array Expr := #[]
  let mut current := list
  let mut limit := 10000
  while limit > 0 do
    limit := limit - 1
    let node ← withTransparency .all (whnf current)
    if node.isAppOfArity ``List.nil 1 then return elems
    if node.isAppOfArity ``List.cons 3 then
      let args := node.getAppArgs
      elems := elems.push args[1]!
      current := args[2]!
    else
      throwError "exprListElems: could not reduce list (stuck at {node})"
  throwError "exprListElems: list exceeded iteration limit"
```

A `List α` in Lean's kernel is either `List.nil` (one argument: the type) or
`List.cons head tail` (three arguments: type, head, tail).  `exprListElems`
iteratively reduces the list expression and peels off one element at a time,
accumulating them into an array.  The 10000-element limit is a safety guard
against accidentally infinite loops.

The loop is written iteratively rather than recursively because Lean's
termination checker cannot easily verify recursive meta-level functions that
descend into arbitrary `Expr` trees.

# Grid Utilities

## Building Concrete Expressions: `mkConcreteFin` and `mkConcretePos`

```
def mkConcreteFin (n val : Nat) : TacticM Expr := do
  let nE   := mkNatLit n
  let valE := mkNatLit val
  let ltProof ← proveByNativeDecide (← mkAppM ``LT.lt #[valE, nE])
  mkAppOptM ``Fin.mk #[some nE, some valE, some ltProof]
```

These helpers construct concrete `Fin` and `Pos` expressions *as Lean kernel
terms* rather than as surface-syntax strings.  `mkNatLit` creates a literal
natural number expression.  `mkAppM` applies a constant to a list of argument
expressions.  `mkAppOptM` is the same but lets you pass `none` for arguments
that should be inferred.  The `ltProof` is produced by `proveByNativeDecide`,
which compiles `val < n` to native code and evaluates it.

## Checking Visibility: `checkSees2d`

```
def checkSees2d (puzExpr : Expr) (rows cols r1 c1 r2 c2 : Nat) : TacticM Bool := do
  if r1 == r2 && c1 == c2 then return false
  if r1 == r2 then
    let lo := min c1 c2 + 1
    let hi := max c1 c2
    for ci in List.range (hi - lo) do
      let c := lo + ci
      let pos ← mkConcretePos rows cols r1 c
      if !(← isCellWhite puzExpr pos) then return false
    return true
  else if c1 == c2 then
    ...
  else
    return false
```

`checkSees2d` mirrors the `Sees` predicate from `Akari.Basic` but operates on
concrete `Nat` coordinates at the meta level.  For each intermediate cell on the
shared row or column, it builds a concrete `Pos` expression with `mkConcretePos`
and queries `isCellWhite` by reducing `puz.cells pos` with `.all` transparency.
It returns a plain `Bool` (not a proposition), which can be used directly in
`if`-branches inside the tactic implementation.

# The Tactics

## `forced_xs`: Forcing an Empty Cell

```
syntax (name := forced_xs) "forced_xs " term : tactic

@[tactic forced_xs] def evalForcedXs : Tactic := fun stx => do
  match stx with
  | `(tactic| forced_xs $posStx) => withMainContext do
    let target   ← getMainTarget
    let (_, solExpr) ← parseSolutionGoal target
    let solStx   ← Lean.PrettyPrinter.delab solExpr
    let hName    := mkIdent (← mkFreshBinderNameForTactic `hempty)
    evalTactic (← `(tactic| have $hName : $posStx ∉ $solStx := by native_decide))
  | _ => throwUnsupportedSyntax
```

The `syntax` declaration introduces the tactic syntax `forced_xs <pos>`.  The
`@[tactic forced_xs]` attribute registers `evalForcedXs` as its elaborator.

When the tactic runs, it:

1. Parses the goal to get `solExpr` (the solution `Finset`).
2. Converts `solExpr` back to surface syntax with `delab` so it can be embedded
   in a quoted tactic.
3. Generates a fresh hypothesis name like `hempty_1`.
4. Emits `have hempty_1 : <pos> ∉ <sol> := by native_decide`, which the kernel
   verifies by compiling and evaluating the proposition.

The backtick-quote notation `` `(tactic| ...) `` is *macro hygiene* — it builds
a `Syntax` value representing a tactic, with `$posStx` and `$solStx` as
metavariables spliced in at run time.

## `suffocated`: Deriving a Contradiction

```
syntax (name := suffocated) "suffocated " term : tactic

@[tactic suffocated] def evalSuffocated : Tactic := fun stx => do
  withMainContext do
    let lctx ← getLCtx
    let mut solGoalOpt : Option (Expr × Expr) := none
    for hyp in lctx do
      let ty ← whnf hyp.type
      let (fn, args) := ty.getAppFnArgs
      if fn == ``Akari.IsSolution && args.size == 2 then
        solGoalOpt := some (args[0]!, args[1]!)
        break
    ...
    evalTactic (← `(tactic| native_decide))
```

`suffocated pos` is used in contradiction sub-proofs where the current goal is
`False`.  A typical scenario: a numbered black cell has fewer available neighbors
than its digit requires, so the puzzle constraints are unsatisfiable — `False`
holds.

Because the current goal is `False` (not `IsSolution ...`), `parseSolutionGoal`
would fail.  Instead, `suffocated` searches the *hypothesis* context (`getLCtx`)
for an `IsSolution puz sol` fact.  Once it finds the puzzle and solution, it
calls `native_decide` directly on the current `False` goal; `native_decide` can
close `False` by evaluating the concrete contradiction.

## `forced_bulbs`: Deriving Forced Bulbs (Uniqueness)

```
syntax (name := forced_bulbs) "forced_bulbs " term : tactic
```

`forced_bulbs pos` is for *uniqueness* proofs, where the hypothesis
`h : IsSolution puz sol` is in context and the goal is `sol = mySolution`.

Unlike the old `forced_lights` tactic (which used `native_decide`), `forced_bulbs`
generates proof terms that invoke the mathematical lemma
`IsSolution.forced_bulb` from `Akari/Basic.lean`.  For each neighbor `q` of the
black cell at `pos`, it emits:

```
have hbulb_1 : ⟨r, c⟩ ∈ sol :=
  IsSolution.forced_bulb h ⟨pr, pc⟩ ⟨n, by decide⟩
    (by decide) ⟨r, c⟩ (by decide) (by decide)
```

The four `by decide` sub-goals verify (a) the cell type, (b) each neighbor's
membership in `getNeighbors`, and (c) the neighbor count equals the cell digit.
These are all ground propositions that `decide` can check.

Using `IsSolution.forced_bulb` rather than `native_decide` is important:
uniqueness proofs are checked at the *kernel* level, where native compilation
results are not trusted.  `forced_bulb` produces an ordinary proof tree
that the kernel can verify step by step.

## `mark_conflict_xs`: Propagating Conflicts (Uniqueness)

`mark_conflict_xs` is the uniqueness counterpart to the deleted `mark_lit_xs`.
It scans every grid position, identifies cells visible from a placed bulb
(using `checkSees2d`), and adds:

```
have hempty_1 : ⟨r, c⟩ ∉ sol :=
  IsSolution.forced_empty_of_sees h ⟨r, c⟩ ⟨br, bc⟩ hbulb_1
    (by decide) (by decide)
```

The `by decide` sub-goals verify that `⟨r, c⟩ ≠ ⟨br, bc⟩` and that
`Sees myPuzzle ⟨r, c⟩ ⟨br, bc⟩` holds.  As with `forced_bulbs`, the lemma
`IsSolution.forced_empty_of_sees` keeps the proof kernel-verifiable.

The tactic tracks which bulb hypothesis justified each empty cell so it can
pass the correct `hbulb_i` name to the lemma.

## `uniqueness_done`: Closing an Equality Goal

```
@[tactic uniqueness_done] def evalUniquenessDone : Tactic := fun _stx => do
  withMainContext do
    evalTactic (← `(tactic| ext p))
    evalTactic (← `(tactic| fin_cases p))
    evalTactic (← `(tactic| all_goals simp_all (config := { decide := true })))
```

After `forced_bulbs` and `mark_conflict_xs` have accumulated enough
`hbulb_i`/`hempty_j` facts, `uniqueness_done` closes the goal `sol = mySolution`.

- `ext p` applies `Finset.ext`: two finite sets are equal iff every element `p`
  belongs to both or neither.  This turns the equality goal into
  `∀ p, p ∈ sol ↔ p ∈ mySolution`.
- `fin_cases p` enumerates every concrete position in `puz.Pos` (all nine cells
  of a 3×3 puzzle, for example), generating one sub-goal per position.
- `simp_all (config := { decide := true })` closes each sub-goal by simplification
  combined with `decide`, using the `hbulb_i`/`hempty_j` hypotheses in context.

## `akari_done`: Closing a Verification Goal

```
@[tactic akari_done] def evalAkariDone : Tactic := fun _stx => do
  withMainContext do
    evalTactic (← `(tactic| constructor))
    -- no_conflicts
    Lean.Elab.Tactic.focus do
      evalTactic (← `(tactic| rw [Akari.NoBulbConflicts]))
      evalTactic (← `(tactic| intro p1 p2 neq h1 h2))
      evalTactic (← `(tactic| fin_cases h1 <;> fin_cases h2))
      evalTactic (← `(tactic| all_goals (dsimp [Akari.Sees]; simp_all; try decide)))
    -- all_lit
    Lean.Elab.Tactic.focus do
      evalTactic (← `(tactic| intro p))
      evalTactic (← `(tactic| dsimp [Akari.IsIlluminated, Akari.Sees]))
      evalTactic (← `(tactic| fin_cases p <;> decide))
    -- adj_correct
    Lean.Elab.Tactic.focus do
      evalTactic (← `(tactic| intro p))
      evalTactic (← `(tactic| fin_cases p <;> simp_all (config := { decide := true })))
```

`akari_done` closes the goal `IsSolution puz sol` by decomposing it into its
three fields and handling each:

- *`no_conflicts`*: introduces `p1`, `p2`, and their membership hypotheses, then
  uses `fin_cases` to enumerate all pairs, and `dsimp [Sees]` + `decide` to
  check each.
- *`all_lit`*: for each position `p`, uses `fin_cases` + `decide` to verify
  it is either non-white or sees a bulb.
- *`adj_correct`*: for each position `p`, uses `fin_cases` + `simp_all` to
  check the neighbor count.

`Lean.Elab.Tactic.focus` prevents the three blocks from interfering with each
other — each block sees only the sub-goals it is responsible for.

One important limitation: `native_decide` cannot close `IsSolution puz sol`
directly because Lean does not automatically synthesize a `Decidable` instance
for `IsSolution`.  The three-field decomposition bypasses this by reducing each
field to a decidable proposition separately.

# Worked Example: `myPuzzle_unique`

Let us trace through the complete uniqueness proof for the 3×3 example:

```
theorem myPuzzle_unique : ∀ sol, IsSolution myPuzzle sol → sol = mySolution := by
  intro sol h
  forced_bulbs ⟨1, 1⟩
  mark_conflict_xs
  uniqueness_done
```

*After `intro sol h`:*
Context contains `sol : Finset myPuzzle.Pos` and `h : IsSolution myPuzzle sol`.
Goal: `sol = mySolution`.

*After `forced_bulbs ⟨1, 1⟩`:*
The cell at `⟨1, 1⟩` is `Cell.black (some 4)`.  `getNeighbors myPuzzle ⟨1, 1⟩`
returns the four cardinal neighbors: `⟨0, 1⟩`, `⟨2, 1⟩`, `⟨1, 0⟩`, `⟨1, 2⟩`.
The neighbor list has length 4, matching the cell's digit.  So `forced_bulbs`
adds four hypotheses:

```
hbulb_1 : ⟨0, 1⟩ ∈ sol
hbulb_2 : ⟨2, 1⟩ ∈ sol
hbulb_3 : ⟨1, 0⟩ ∈ sol
hbulb_4 : ⟨1, 2⟩ ∈ sol
```

*After `mark_conflict_xs`:*
Each of the four bulbs illuminates cells in its row and column.  The four corner
cells `⟨0, 0⟩`, `⟨0, 2⟩`, `⟨2, 0⟩`, `⟨2, 2⟩` are each visible from at least
one bulb, so `mark_conflict_xs` adds:

```
hempty_1 : ⟨0, 0⟩ ∉ sol
hempty_2 : ⟨0, 2⟩ ∉ sol
hempty_3 : ⟨2, 0⟩ ∉ sol
hempty_4 : ⟨2, 2⟩ ∉ sol
```

The center cell `⟨1, 1⟩` is black, so it never enters `sol`.

*After `uniqueness_done`:*
`ext p` reduces the goal to nine membership sub-goals.  `fin_cases p` generates
one sub-goal per grid position.  For positions in `{⟨0,1⟩, ⟨1,0⟩, ⟨1,2⟩, ⟨2,1⟩}`,
the relevant `hbulb_i` confirms membership.  For the four corners, the relevant
`hempty_j` refutes membership.  For `⟨1,1⟩`, the cell is black so `decide`
verifies it is not in `mySolution` directly.  All nine sub-goals close, and the
proof is complete.
