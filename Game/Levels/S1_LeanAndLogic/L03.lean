import Game.Metadata

World "LeanAndLogic"
Level 3

Title "Conjunction, Equivalence, and Negation"

Introduction "
This level is the scaffold for Lecture L03 of Math 323.
Topic: Conjunction, equivalence, and negation.
"

Statement (x y : Nat) (h : x = 2) (g: y = 4) : y = y := by
  rfl

Conclusion "This last message appears if the level is solved."

NewTactic dsimp constructor rintro
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
