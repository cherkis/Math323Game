import Game.Metadata

World "SupremumInfimum"
Level 2

Title "Infimum"

Introduction "
This level is the scaffold for Lecture L23 of Math 323.
Topic: Infimum, separation theorems, and nested intervals.
"

Statement (x y : Nat) (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

NewTactic BddBelow lowerBounds IsGLB csInf_le le_csInf
