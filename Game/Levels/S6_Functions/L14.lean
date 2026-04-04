import Game.Metadata

World "Functions"
Level 1

Title "Injections and Surjections"

Introduction "
This level is the scaffold for Lecture L14 of Math 323.
Topic: Injections, surjections, bijections, and composition.
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

NewTactic funext
