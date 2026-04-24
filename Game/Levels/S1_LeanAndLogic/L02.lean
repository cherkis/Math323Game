import Game.Metadata

World "LeanAndLogic"
Level 2

Title "Implication, False, and True"

Introduction "
This level is the scaffold for Lecture L02 of Math 323.
Topic: Implication, False, True, and tactic mode basics.
"

Statement (x y : Nat) (h : x = 2) (g: y = 4) : y = y := by
  rfl

Conclusion "This last message appears if the level is solved."

NewTactic contradiction exfalso obtain
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
