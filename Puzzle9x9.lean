import Akari
import Akari.Tactics.Basic
import Akari.Widget
import Mathlib.Tactic
open Akari Akari.Tactics

/-!
# A real 9×9 Akari puzzle

The grid (coordinates are `(row, col)`, 0-indexed):

```
. . . . . . . . .
. . . . . . . . .
. . . 1 . . . . .
. . . . . 1 . . .
. . 1 . . . . . .
. . . . . . 1 . .
. 1 . . . . . . .
. . . . . . . 3 .
1 . . . . . . . 2
```

Black numbered cells:
  (2,3)=1  (3,5)=1  (4,2)=1  (5,6)=1
  (6,1)=1  (7,7)=3  (8,0)=1  (8,8)=2
-/

abbrev puzzle9x9 : Puzzle where
  rows := 9
  cols := 9
  cells p :=
    if      p == ⟨2,3⟩ then Cell.black (some 1)
    else if p == ⟨3,5⟩ then Cell.black (some 1)
    else if p == ⟨4,2⟩ then Cell.black (some 1)
    else if p == ⟨5,6⟩ then Cell.black (some 1)
    else if p == ⟨6,1⟩ then Cell.black (some 1)
    else if p == ⟨7,7⟩ then Cell.black (some 3)
    else if p == ⟨8,0⟩ then Cell.black (some 1)
    else if p == ⟨8,8⟩ then Cell.black (some 2)
    else Cell.white

/-- The known solution: 10 bulbs. -/
abbrev solution9x9 : Finset puzzle9x9.Pos :=
  {⟨0,4⟩, ⟨1,3⟩, ⟨2,5⟩, ⟨3,2⟩, ⟨4,6⟩, ⟨5,1⟩, ⟨6,7⟩, ⟨7,0⟩, ⟨7,8⟩, ⟨8,7⟩}

-- Profiling: uncomment the two `set_option`s below (and temporarily drop the
-- `with_panel_widgets` wrapper, which otherwise collapses the whole block into a
-- single profiler step) to see per-tactic wall-clock times. Last measured (~8.4s):
--   uniqueness_done .......... 5.22s   (kernel `decide` bridge + fin_cases over 81)
--   8× forced_bulbs chain .... ~2.34s  (0.44s → 0.13s, shrinking as cells get X'd)
--   forced_lit ⟨0,4⟩ ......... 0.26s
-- Note: `#count_heartbeats in` reports only ~18 here — heartbeats don't bill the
-- native_decide / kernel `decide` work that dominates; trace.profiler does.
-- set_option trace.profiler true in
-- set_option trace.profiler.threshold 30 in
set_option linter.unusedTactic false in
theorem puzzle9x9_unique : ∀ sol, IsSolution puzzle9x9 sol → sol = solution9x9 := by with_panel_widgets [AkariPanelWidget]
  intro sol h
  -- Each `forced_bulbs` now counts only *free* (not-yet-X'd) neighbours and
  -- auto-runs `mark_conflict_xs`, so a #n cell fires once enough siblings are X'd.
  -- The order below chains those deductions; the cursor on any line shows progress.
  forced_bulbs ⟨8, 8⟩   -- #2 corner → bulbs (7,8),(8,7)
  forced_bulbs ⟨8, 0⟩   -- #1: (8,1) X'd by (8,7) → bulb (7,0)
  forced_bulbs ⟨7, 7⟩   -- #3: (7,6) X'd by (7,0) → bulb (6,7)
  forced_bulbs ⟨6, 1⟩   -- #1: (7,1),(6,0) by (7,0); (6,2) by (6,7) → bulb (5,1)
  forced_bulbs ⟨5, 6⟩   -- #1: (5,5) by (5,1); (5,7),(6,6) by (6,7) → bulb (4,6)
  forced_bulbs ⟨4, 2⟩   -- #1: (5,2),(4,1) by (5,1); (4,3) by (4,6) → bulb (3,2)
  forced_bulbs ⟨3, 5⟩   -- #1: (4,5),(3,6) by (4,6); (3,4) by (3,2) → bulb (2,5)
  forced_bulbs ⟨2, 3⟩   -- #1: (3,3),(2,2) by (3,2); (2,4) by (2,5) → bulb (1,3)
  forced_lit ⟨0, 4⟩
  uniqueness_done
