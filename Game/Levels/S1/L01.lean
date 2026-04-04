import Game.Metadata

World "Propositional Logic"
Level 1

Title "Introduction to Lean"

Introduction "Let us start with a few Lean tactics to handle basic logic operations. For each proposition we need to learn how
- go about proving it (if that is our goal) or
- how to use it (if it is one of our hypotheses)."

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

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
