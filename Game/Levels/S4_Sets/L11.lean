import Game.Metadata

World "Sets"
Level 2

Title "Power Sets and De Morgan Laws"

Introduction "
This level is the scaffold for Lecture L11 of Math 323.
Topic: Indexed families, power sets, and De Morgan laws.
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

NewTactic push_neg
