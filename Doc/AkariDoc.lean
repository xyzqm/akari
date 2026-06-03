import VersoManual
import AkariDoc.Basics
import AkariDoc.Tactics

open Verso.Genre Manual

#doc (Manual) "Akari (Light Up) in Lean 4" =>

%%%
authors := [""]
%%%

This book explains how the Akari (Light Up) puzzle is formalized and solved in Lean 4.
It is intended for readers who are comfortable with general programming concepts but
are not necessarily familiar with Lean or formal proof assistants.

The first chapter covers all the core data types and logical predicates defined in
`Akari/Basic.lean`. The second chapter explains the custom proof tactics in
`Akari/Tactics/Basic.lean`.

{include 1 AkariDoc.Basics}

{include 1 AkariDoc.Tactics}
