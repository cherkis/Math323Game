import GameServer
-- import Mathlib.Tactic.Common
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.NormNum

set_option warningAsError false

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file Lean file per world
which imports all its levels.
-/
