import Game.Metadata

World "SequencesLimits"
Level 2

Title "Monotone and Cauchy Sequences"

Introduction "
This level is the scaffold for Lecture L25 of Math 323.
Topic: Monotone sequences and Cauchy sequences.
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

NewTactic Filter.Tendsto
