import Game.Metadata

World "Relations"
Level 2

Title "Quotients and Residue Classes"

Introduction "
This level is the scaffold for Lecture L13 of Math 323.
Topic: Quotient types, well-definedness, and residue classes.
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

NewTactic Quotient.mk Quotient.sound Quotient.exact Quotient.lift Quotient.lift₂ Quotient.ind rename_i congr
