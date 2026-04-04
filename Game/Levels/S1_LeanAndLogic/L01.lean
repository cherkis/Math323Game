import Game.Metadata

World "LeanAndLogic"
Level 1

Title "Type Theory and Lean Syntax"

Introduction "
This level is the scaffold for Lecture L01 of Math 323.
Topic: Type theory, Lean syntax, and term-mode proofs.
"

Statement (x y : Nat) (h : x = 2) (g: y = 4) : y = y := by
  rfl
--  Hint "You can either start using `{h}` or `{g}`."
--  Branch
  --   rw [g]
  --   Hint "You should use `{h}` now."
  --   rw [h]
  -- rw [h]
  -- Hint "You should use `{g}` now."
  -- rw [g]

Conclusion "This last message appears if the level is solved."

NewTactic rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
