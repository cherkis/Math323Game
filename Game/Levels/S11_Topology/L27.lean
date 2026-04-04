import Game.Metadata

World "Topology"
Level 2

Title "Compactness and Continuity"

Introduction "
This level is the scaffold for Lecture L27 of Math 323.
Topic: Compactness, continuity, and Heine-Borel.
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

NewTactic Continuous IsCompact Filter.Eventually
