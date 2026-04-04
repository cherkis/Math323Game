import Game.Metadata

World "Cardinality"
Level 3

Title "Unique Existence"

Introduction "
This level is the scaffold for Lecture L18 of Math 323.
Topic: Classical witness extraction and unique existence.
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

NewTactic Classical.choose Classical.choose_spec
