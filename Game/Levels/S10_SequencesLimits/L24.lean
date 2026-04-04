import Game.Metadata

World "SequencesLimits"
Level 1

Title "Limits of Sequences"

Introduction "
This level is the scaffold for Lecture L24 of Math 323.
Topic: Epsilon-N definitions of limits.
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

NewTactic specialize use abs_sub_comm abs_le
