import Game.Metadata

World "Functions"
Level 2

Title "Image, Preimage, and Inverses"

Introduction "
This level is the scaffold for Lecture L15 of Math 323.
Topic: Image, preimage, inverses, and the axiom of choice.
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

-- Additional lecture tactic from the plan not representable in `NewTactic`: exact?
NewTactic choose aesop
