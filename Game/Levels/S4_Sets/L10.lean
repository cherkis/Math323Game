import Game.Metadata

World "Sets"
Level 1

Title "Sets as Predicates"

Introduction "
This level is the scaffold for Lecture L10 of Math 323.
Topic: Sets as predicates, membership, operations, and extensionality.
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

-- Additional lecture tactics from the plan not representable in `NewTactic`: show, change, suffices, simp only
NewTactic ext simp tauto
