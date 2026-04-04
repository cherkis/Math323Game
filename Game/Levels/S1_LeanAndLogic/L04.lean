import Game.Metadata

World "LeanAndLogic"
Level 4

Title "Disjunction and Case Splits"

Introduction "
This level is the scaffold for Lecture L04 of Math 323.
Topic: Disjunction, case splits, and first rewrites.
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

-- Additional lecture tactic from the plan not representable in `NewTactic`: have
NewTactic left right obtain rcases by_cases rw
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
