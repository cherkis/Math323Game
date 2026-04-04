import Game.Metadata

World "Induction"
Level 2

Title "Dependent Types and Exploration"

Introduction "
This level is the scaffold for Lecture L08 of Math 323.
Topic: Sigma and Pi types, dependent types, and library exploration.
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

NewTactic ring norm_num
